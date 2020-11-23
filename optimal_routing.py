#!/usr/bin/python3

from ryu.base import app_manager
from ryu.controller import mac_to_port
from ryu.controller import ofp_event
from ryu.controller.handler import CONFIG_DISPATCHER, MAIN_DISPATCHER
from ryu.controller.handler import set_ev_cls
from ryu.ofproto import ofproto_v1_3
from ryu.lib.mac import haddr_to_bin
from ryu.lib.packet import packet
from ryu.lib.packet import arp
from ryu.lib.packet import ethernet
from ryu.lib.packet import ipv4
from ryu.lib.packet import ipv6
from ryu.lib.packet import ether_types
from ryu.lib.packet import udp
from ryu.lib.packet import tcp
from ryu.lib import mac, ip
from ryu.lib import hub
from ryu.ofproto import inet
from ryu.topology.api import get_switch, get_link, get_host
from ryu.app.wsgi import ControllerBase
from ryu.topology import event, switches

from collections import defaultdict
from operator import itemgetter
from dataclasses import dataclass
import heapq
# to implement the background running process
import threading
import os
import random
import time

#Cisco Reference value for bandwidth which is 1Gbps
REFERENCE_BW = 10000000
DEFAULT_BW = 10000000
MAX_PATHS = 1

@dataclass
class Paths:
    ''' Paths container'''
    path: list()
    cost: float


class optimal_algo(app_manager.RyuApp):
    OFP_VERSIONS = [ofproto_v1_3.OFP_VERSION]


    def __init__(self, *args, **kwargs):
        super(optimal_algor, self).__init__(*args, **kwargs)
        self.mac_to_port = {}
        # We store a values in the dictionary inorder to avoid the duplications 
        # The input will take: {SwithId: {Neighbour1:Port_Switches,Neighbour2:Port_Switches}}
        self.neigh = defaultdict(dict) 
        #it is same as before but the value here is [switch][port]
        self.bw = defaultdict(lambda: defaultdict( lambda: DEFAULT_BW)) 
        self.prev_bytes = defaultdict(lambda: defaultdict( lambda: 0)) 
        #It stores in the  EthernetSource:(DPID_of_switch, In_Port)
        self.hosts = {} 
        # To maintain list of switches
        self.switches = [] 
        # Map the mac address to the respective  MAC:PORT
        self.arp_table = {} 
        # The current path of the network structure is (src, in_port, dst, out_port):Path
        self.path_table = {}
        # The probability path of the network  (src, in_port, dst, out_port):Paths        
        self.paths_table = {} 
        # Current network optimal_path structure (src, in_port, dst, out_port):Path_with_ports
        self.path_with_ports_table = {} 
        # Create a dictionary to store the switch dpid and dp [SwitchDPID:SwitchDP]
        self.datapath_list = {} 
        #Create a tuple to calculate the path and store the src address, input port and output port (src, in_port, dst, out_port)
        self.path_calculation_keeper = [] 

    def find_path_cost(self,path):
        ''' arg path is an list with all nodes in our route '''
        path_cost = []
        for i in range(len(path) - 1):
            port1 = self.neigh[path[i]][path[i + 1]]
            #port2 = self.neigh[path[i + 1]][path[i]]
            bandwidth_between_two_nodes = self.bw[path[i]][port1]
            #path_cost.append(REFERENCE_BW / bandwidth_between_two_nodes)
            path_cost.append(bandwidth_between_two_nodes)
        return sum(path_cost)

    def find_paths_and_costs(self, source, destination):
        ''' 
        Implementation of Breath-First Search (BFS) Algorithm
        Take the starting node as source and ending node as destination
        Used queues to make the track of the visited nodes
        Output of this function returns an list on class Paths objects
        ''' 
        # if the source and destination address is the same return to the path function
        if source == destination:
            # print("Source is the same as destination ! ")
            return [Paths(source,0)]
        queue = [(source, [source])]
        # The possible path list can be commented out if we use generator
        possible_paths = list() 
        # if elements in the queue exists
        while queue:
             # if there are no adjacent vertices left, remove the first element from the queue
            (edge, path) = queue.pop()
            # iterate the loop to perform the visiting node and mark it as display and insert the element in the queue
            for vertex in set(self.neigh[edge]) - set(path):
            # Repeat the above steps until we find out the desired element from the queue. Until then perform removing the element 
                if vertex == destination:
                    path_to_dst = path + [vertex]
                    cost_of_path = self.find_path_cost(path_to_dst)
                    possible_paths.append(Paths(path_to_dst, cost_of_path))
                else:
                    queue.append((vertex, path + [vertex]))
        return possible_paths 
           
    def find_n_optimal_paths(self, paths, number_of_optimal_paths = MAX_PATHS):
        '''arg Paths is an list containing lists of possible paths'''
        costs = [path.cost for path in paths]
        index_of_optimal_path = list(map(costs.index, heapq.nsmallest(number_of_optimal_paths,costs)))
        optimal_paths = [paths[op_index] for op_index in index_of_optimal_path]
        return optimal_paths
    
    def add_ports_to_paths(self, paths, f_port, l_port):
        '''
        Add the ports to all switches including hosts
        '''
        port_path = list()
        # bf is a dict to store the dpid in the format of ingress port and egress port switchDPID:(Ingress_Port, Egress_Port)
        bf = {} 
        in_port = f_port
        for s1, s2 in zip(paths[0].path[:-1], paths[0].path[1:]):
            out_port = self.neigh[s1][s2]
            bf[s1] = (in_port, out_port)
            in_port = self.neigh[s2][s1]
        bf[paths[0].path[-1]] = (in_port, l_port)
        port_path.append(bf)
        return port_path

    def install_paths(self, src, f_port, dest, l_port, ip_src, ip_dst, type, pkt):
        ''' Instalacja sciezek '''
        # self.topology_discover(src, f_port, dst, l_port) 

        if (src, f_port, dst, l_port) not in self.path_calculation_keeper:
            self.path_calculation_keeper.append((src, f_port, dst, l_port))
            self.topology_discover(src, f_port, dest, l_port)
            self.topology_discover(dest, l_port, src, f_port)

        
        for node in self.path_table[(src, f_port, dest, l_port)][0].path:

            dp = self.datapath_list[node]
            ofp = dp.ofproto
            ofp_parser = dp.ofproto_parser

            actions = []

            in_port = self.path_with_ports_table[(src, f_port, dest, l_port)][0][node][0]
            out_port = self.path_with_ports_table[(src, f_port, dest, l_port)][0][node][1]
                
            actions = [ofp_parser.OFPActionOutput(out_port)]

            if type == 'UDP':
                nw = pkt.get_protocol(ipv4.ipv4)
                l4 = pkt.get_protocol(udp.udp)

                match = ofp_parser.OFPMatch(in_port = in_port,
                                        eth_type=ether_types.ETH_TYPE_IP, 
                                        ipv4_src=ip_src,
                                        ipv4_dst = ip_dst, 
                                        ip_proto=inet.IPPROTO_UDP,
                                        udp_src = l4.src_port, 
                                        udp_dst = l4.dst_port)

                self.logger.info(f"Installed path in switch: {node} out port: {out_port} in port: {in_port} ")
                
                self.add_flow(dp, 33333, match, actions, 10)
                self.logger.info("UDP Flow added ! ")
            
            elif type == 'TCP':

                nw = pkt.get_protocol(ipv4.ipv4)
                l4 = pkt.get_protocol(tcp.tcp)

                match = ofp_parser.OFPMatch(in_port = in_port,
                                        eth_type=ether_types.ETH_TYPE_IP, 
                                        ipv4_src=ip_src, 
                                        ipv4_dst = ip_dst, 
                                        ip_proto=inet.IPPROTO_TCP,
                                        tcp_src = l4.src_port, 
                                        tcp_dst = l4.dst_port)

                self.logger.info(f"Installed path in switch: {node} out port: {out_port} in port: {in_port} ")
                
                self.add_flow(dp, 44444, match, actions, 10)
                self.logger.info("TCP Flow added ! ")

            elif type == 'ICMP':

                nw = pkt.get_protocol(ipv4.ipv4)

                match = ofp_parser.OFPMatch(in_port=in_port,
                                        eth_type=ether_types.ETH_TYPE_IP, 
                                        ipv4_src=ip_src, 
                                        ipv4_dst = ip_dst, 
                                        ip_proto=inet.IPPROTO_ICMP)

                self.logger.info(f"Installed path in switch: {node} out port: {out_port} in port: {in_port} ")
                
                
                self.add_flow(dp, 22222, match, actions, 10)
                self.logger.info("ICMP Flow added ! ")

            elif type == 'ARP':
                match_arp = ofp_parser.OFPMatch(in_port = in_port,
                                                eth_type=ether_types.ETH_TYPE_ARP, 
                                                arp_spa=ip_src, 
                                                arp_tpa=ip_dst)

                self.logger.info(f"Install path in switch: {node} out port: {out_port} in port: {in_port} ")
                
                self.add_flow(dp, 1, match_arp, actions, 10)
                self.logger.info("ARP Flow added ! ")
        
        #return self.path_with_ports_table[0][src][1]
        return self.path_with_ports_table[(src, f_port, dest, l_port)][0][src][1]

    def add_flow(self, datapath, priority, match, actions, idle_timeout, buffer_id = None):
        ''' Method Provided by the source Ryu library. '''
        #To use openflow library
        ofproto = datapath.ofproto 
        parser = datapath.ofproto_parser 

        inst = [parser.OFPInstructionActions(ofproto.OFPIT_APPLY_ACTIONS,
                                             actions)]
        if buffer_id:
            mod = parser.OFPFlowMod(datapath=datapath, buffer_id=buffer_id,
                                    priority=priority, match=match, idle_timeout = idle_timeout,
                                    instructions=inst)
        else:
            mod = parser.OFPFlowMod(datapath=datapath, priority=priority,
                                    match=match, idle_timeout = idle_timeout, instructions=inst)
        datapath.send_msg(mod)
    
    def run_check(self, ofp_parser, dp):
        ''' Co sekunde watek wypytuje switche o status portow i wysylany jest PortStatsReq'''
        threading.Timer(1.0, self.run_check, args=(ofp_parser, dp)).start()
        
        req = ofp_parser.OFPPortStatsRequest(dp) 
        #self.logger.info(f"Port Stats Request has been sent for sw: {dp} !")
        dp.send_msg(req)

    def topology_discover(self, src, f_port, dest, l_port):
        ''' Obliczanie optymalnej sciezki dla zadanych parametrow + przypisanie portow '''
        threading.Timer(1.0, self.topology_discover, args=(src, f_port, dest, l_port)).start()
        paths = self.find_paths_and_costs(src, dest)
        path = self.find_n_optimal_paths(paths)
        path_with_port = self.add_ports_to_paths(path, f_port, l_port)
        
        self.logger.info(f"Possible paths: {paths}")
        self.logger.info(f"Optimal Path with port: {path_with_port}")
        
        self.paths_table[(src, f_port, dest, l_port)]  = paths
        self.path_table[(src, f_port, dest, l_port)] = path
        self.path_with_ports_table[(src, f_port, dest, l_port)] = path_with_port


    @set_ev_cls(ofp_event.EventOFPPacketIn, MAIN_DISPATCHER)
    def _packet_in_handler(self, ev):
        if ev.msg.msg_len < ev.msg.total_len:
            self.logger.debug("packet truncated: only %s of %s bytes", ev.msg.msg_len, ev.msg.total_len)
        msg = ev.msg
        datapath = msg.datapath
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        in_port = msg.match['in_port']

        pkt = packet.Packet(msg.data)
        eth = pkt.get_protocols(ethernet.ethernet)[0]
        arp_pkt = pkt.get_protocol(arp.arp)
        ip_pkt = pkt.get_protocol(ipv4.ipv4)
        
        if eth.ethertype == ether_types.ETH_TYPE_LLDP:
            # ignore lldp packet
            return

        dst = eth.dst
        src = eth.src
        dpid = datapath.id
        
        if src not in self.hosts:
            self.hosts[src] = (dpid, in_port)

        out_port = ofproto.OFPP_FLOOD

        if eth.ethertype == ether_types.ETH_TYPE_IP:
            nw = pkt.get_protocol(ipv4.ipv4)
            if nw.proto == inet.IPPROTO_UDP:
                l4 = pkt.get_protocol(udp.udp)
            elif nw.proto == inet.IPPROTO_TCP:
                l4 = pkt.get_protocol(tcp.tcp)     

        if eth.ethertype == ether_types.ETH_TYPE_IP and nw.proto == inet.IPPROTO_UDP:
            src_ip = nw.src
            dst_ip = nw.dst
            
            self.arp_table[src_ip] = src
            h1 = self.hosts[src]
            h2 = self.hosts[dst]

            self.logger.info(f" IP Proto UDP from: {nw.src} to: {nw.dst}")

            out_port = self.install_paths(h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip, 'UDP', pkt)
            self.install_paths(h2[0], h2[1], h1[0], h1[1], dst_ip, src_ip, 'UDP', pkt) 
        
            
        elif eth.ethertype == ether_types.ETH_TYPE_IP and nw.proto == inet.IPPROTO_TCP:
            src_ip = nw.src
            dst_ip = nw.dst
            
            self.arp_table[src_ip] = src
            h1 = self.hosts[src]
            h2 = self.hosts[dst]

            self.logger.info(f" IP Proto TCP from: {nw.src} to: {nw.dst}")

            out_port = self.install_paths(h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip, 'TCP', pkt)
            self.install_paths(h2[0], h2[1], h1[0], h1[1], dst_ip, src_ip, 'TCP', pkt) 

        elif eth.ethertype == ether_types.ETH_TYPE_IP and nw.proto == inet.IPPROTO_ICMP:
            src_ip = nw.src
            dst_ip = nw.dst
            
            self.arp_table[src_ip] = src
            h1 = self.hosts[src]
            h2 = self.hosts[dst]

            self.logger.info(f" IP Proto ICMP from: {nw.src} to: {nw.dst}")

            out_port = self.install_paths(h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip, 'ICMP', pkt)
            self.install_paths(h2[0], h2[1], h1[0], h1[1], dst_ip, src_ip, 'ICMP', pkt)

        elif eth.ethertype == ether_types.ETH_TYPE_ARP:
            src_ip = arp_pkt.src_ip
            dst_ip = arp_pkt.dst_ip

            if arp_pkt.opcode == arp.ARP_REPLY:
                self.arp_table[src_ip] = src
                h1 = self.hosts[src]
                h2 = self.hosts[dst]

                self.logger.info(f" ARP Reply from: {src_ip} to: {dst_ip} H1: {h1} H2: {h2}")

                out_port = self.install_paths(h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip, 'ARP', pkt)
                self.install_paths(h2[0], h2[1], h1[0], h1[1], dst_ip, src_ip, 'ARP', pkt) 

            elif arp_pkt.opcode == arp.ARP_REQUEST:
                if dst_ip in self.arp_table:
                    self.arp_table[src_ip] = src
                    dst_mac = self.arp_table[dst_ip]
                    h1 = self.hosts[src]
                    h2 = self.hosts[dst_mac]

                    self.logger.info(f" ARP Reply from: {src_ip} to: {dst_ip} H1: {h1} H2: {h2}")

                    out_port = self.install_paths(h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip, 'ARP', pkt)
                    self.install_paths(h2[0], h2[1], h1[0], h1[1], dst_ip, src_ip, 'ARP', pkt)

        actions = [parser.OFPActionOutput(out_port)]
        
        data = None

        if msg.buffer_id == ofproto.OFP_NO_BUFFER:
            data = msg.data

        out = parser.OFPPacketOut(datapath=datapath, buffer_id=msg.buffer_id, 
                                    in_port=in_port, actions=actions, data=data)
        datapath.send_msg(out)

    @set_ev_cls(ofp_event.EventOFPSwitchFeatures, CONFIG_DISPATCHER)
    def _switch_features_handler(self, ev):
        ''' 
        To send packets for which we dont have right information to the controller
        Method Provided by the source Ryu library. 
        '''

        datapath = ev.msg.datapath
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        
        match = parser.OFPMatch()
        actions = [parser.OFPActionOutput(ofproto.OFPP_CONTROLLER,
                                          ofproto.OFPCML_NO_BUFFER)]
        self.add_flow(datapath, 0, match, actions, 10)

    @set_ev_cls(ofp_event.EventOFPPortStatsReply, MAIN_DISPATCHER)
    def _port_stats_reply_handler(self, ev):
        '''Reply to the OFPPortStatsRequest, visible beneath'''
        switch_dpid = ev.msg.datapath.id
        for p in ev.msg.body:
            # stores the port information in Mbit/s
            self.bw[switch_dpid][p.port_no] = (p.tx_bytes - self.prev_bytes[switch_dpid][p.port_no])*8.0/1000000 
            self.prev_bytes[switch_dpid][p.port_no] = p.tx_bytes
            

            #self.logger.info(f"Switch: {switch_dpid} Port: {p.port_no} Tx bytes: {p.tx_bytes} Bw: {self.bw[switch_dpid][p.port_no]}")

    @set_ev_cls(event.EventSwitchEnter)
    def switch_enter_handler(self, ev):
        switch_dp = ev.switch.dp
        switch_dpid = switch_dp.id
        ofp_parser = switch_dp.ofproto_parser
        
        self.logger.info(f"Switch has been plugged in PID: {switch_dpid}")
            
        if switch_dpid not in self.switches:
            self.datapath_list[switch_dpid] = switch_dp
            self.switches.append(switch_dpid)
            #function which runs in the bakground every 1 second
            self.run_check(ofp_parser, switch_dp)  

    @set_ev_cls(event.EventSwitchLeave, MAIN_DISPATCHER)
    def switch_leave_handler(self, ev):
        switch = ev.switch.dp.id
        if switch in self.switches:
            try:
                self.switches.remove(switch)
                del self.datapath_list[switch]
                del self.neigh[switch]
            except KeyError:
                self.logger.info(f"Switch has been already pulged off PID{switch}!")
            

    @set_ev_cls(event.EventLinkAdd, MAIN_DISPATCHER)
    def link_add_handler(self, ev):
        self.neigh[ev.link.src.dpid][ev.link.dst.dpid] = ev.link.src.port_no
        self.neigh[ev.link.dst.dpid][ev.link.src.dpid] = ev.link.dst.port_no
        self.logger.info(f"Link between switches has been established, SW1 DPID: {ev.link.src.dpid}:{ev.link.dst.port_no} SW2 DPID: {ev.link.dst.dpid}:{ev.link.dst.port_no}")

    @set_ev_cls(event.EventLinkDelete, MAIN_DISPATCHER)
    def link_delete_handler(self, ev):
        try:
            del self.neigh[ev.link.src.dpid][ev.link.dst.dpid] 
            del self.neigh[ev.link.dst.dpid][ev.link.src.dpid] 
        except KeyError:
            self.logger.info("Link has been already pluged off!")
            pass
