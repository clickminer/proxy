'''
Copyright (C) 2012 Chris Neasbitt
Author: Chris Neasbitt

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 2 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
'''
import threading, urlparse, math, json, sys, traceback, urllib, time, os, mimetypes

from libmproxy import utils, flow
from netlib import tcp, http_status, odict
from operator import attrgetter, itemgetter
from StringIO import StringIO
from PIL import Image

# BEGIN mitmproxy hooks

iserver = None

def start(context):
    global iserver
    iserver = InstrumentServer(('', 8888), context._master)
    iserver.daemon = True
    iserver.start()
    if InstrumentServer.DEBUG:
        print "InstrumentServer started."
    
def clientconnect(context, clientconnect):
    global iserver
    iserver.handle_hook_clientconnect(context, clientconnect)
    
def request(context, fl):
    global iserver
    iserver.handle_hook_request(context, fl)
            
def response(context, fl):
    global iserver    
    iserver.handle_hook_response(context, fl)
    
def error(context, fl):
    global iserver    
    iserver.handle_hook_error(context, fl)
    
def done(context):
    global iserver
    iserver.shutdown()
    iserver.join()
    if InstrumentServer.DEBUG:
        print "InstrumentServer stopped."
    
# END mitmproxy hooks


class InstrumentServer(tcp.TCPServer, threading.Thread):

    MIN_REQ = "MIN_REQ"
    PRINT_REQS = "PRINT_REQS"
    RECV_REQ_COUNT = "RECV_REQ_COUNT"
    CMPLT_REQ_COUNT = "CMPLT_REQ_COUNT"
    POS_REQ = "POS_REQ"
    NEXT_POS_REQ = "NEXT_POS_REQ"
    SET_TS = "SET_TS"
    GET_MODE = "GET_MODE"
    SET_MODE_NOCONTENT = "SET_MODE_NOCONTENT"
    SET_MODE_CONTENT = "SET_MODE_CONTENT"
    SET_REQ_CHECK_LIMIT = "SET_REQ_CHECK_LIMIT"
    SET_FILTERED_RESP_TYPE = "SET_FILTERED_RESP_TYPE"
    GET_REQ_CHECK_LIMIT = "GET_REQ_CHECK_LIMIT"
    GET_LAST_REQ_REFERER = "GET_LAST_REQ_REFERER"
    REM_FILTERED_RESP_TYPE = "REM_FILTERED_RESP_TYPE"
    
    
    RESP_ERROR = "ERROR"
    RESP_OK = "OK"
    
    GENERATED_HEADER = "X-Clickminer-Generated"
    
    #a complete flow with one request and a 204 response        
    FLOW_204_STR = "745:5:error,0:~8:response,315:11:httpversion,8:1:1#1:1#]" + \
        "13:timestamp_end,16:1358550895.28548^3:msg,10:No Content,15:timesta" + \
        "mp_start,17:1358550563.343895^7:headers,141:22:14:Content-Length,1:" + \
        "0,]44:12:Content-Type,24:text/html; charset=UTF-8,]40:4:Date,29:Fri" + \
        ", 18 Jan 2013 23:09:12 GMT,]19:6:Server,7:GFE/2.0,]]7:content,0:,4:" + \
        "cert,0:~4:code,3:204#}7:request,367:11:httpversion,8:1:1#1:1#]4:por" + \
        "t,2:80#6:scheme,4:http,4:path,13:/generate_204,4:host,14:www.google" + \
        ".com,11:client_conn,0:~7:content,0:,6:method,3:GET,15:timestamp_sta" + \
        "rt,17:1358550563.343895^7:headers,125:41:10:User-Agent,23:Wget/1.13" + \
        ".4 (linux-gnu),]15:6:Accept,3:*/*,]25:4:Host,14:www.google.com,]28:" + \
        "10:Connection,10:Keep-Alive,]]13:timestamp_end,17:1358550895.285345" + \
        "^}7:version,8:1:0#1:9#]}"
        
    WEB_API_URLS = ["http://www.facebook.com/plugins",
                    "http://platform.twitter.com/widgets",
                    "http://www.linkedin.com/countserv/count/share",
                    "http://badge.stumbleupon.com/badge",
                    "http://partners-api.pinterest.com/v1"]
    
    DEBUG = True

    def __init__(self, server_address, master, path_simil_threshhold = -1.0,
                 param_intersec_threshhold = -1.0, param_values_threshold = -1.0,
                 interleaving_window = 20):
        tcp.TCPServer.__init__(self, server_address)
        self.master = master
        self.totalflowmap = dict() # just in case we need all of the original requests
        self.request_count = 0
        self.complete_request_count = 0
        self.error_count = 0
        self.path_simil_threshhold = path_simil_threshhold
        self.param_intersec_threshhold = param_intersec_threshhold
        self.param_values_threshold = param_values_threshold
        
        # the number of requests in the window chronologically forward
        # and backward from the proxy's current timestamp
        self.interleaving_window = interleaving_window
        self.ts = 0
        self.content_mode = True
        self.content_mode_url = None
        self.skip_ts_update_list = list()
        self.pos_req_list = list() #list of flows
        self.last_pos_req = None #the last possible request sent to the browser
        
        self.req_referer_time_diff = dict() #values are measured in seconds
        self.compute_req_referer_time_diff()
        
        self.num_requests_refered = dict() #for each url key, how many requests have that referer
        self.compute_num_requests_refered()
        
        #stores the number of times a request has been sent to the browser as a possible
        #interaction request
        self.request_check_count = dict()
        
        #the upper limit for the number of times a request should be sent to the browser
        #as a possible interaction request.  0 means no limit  
        self.request_check_limit = 0
        self.last_req_referer = dict()
        self.filtered_resp_types = list() 
        self.init_204_flow()
        
        #store the number of times a request for a url could not be satisfied from
        #the saved flows
        self.request_fail_count = dict()
        #once a request's fail count has reach this limit, instead of returning a
        #404 response we return a 200 response will dummy content 
        self.request_fail_limit = 15
        
        if InstrumentServer.DEBUG:
            self.print_request_in_order()
        
        threading.Thread.__init__(self)
        

    def init_204_flow(self):
        flread = flow.FlowReader(StringIO(self.FLOW_204_STR))
        flstream = flread.stream()
        try:
            self.flow_204 = flstream.next()
        except StopIteration, e:
            if InstrumentServer.DEBUG:
                print e

    def handle_hook_error(self, context, fl):
        self.error_count += 1
    
    def handle_hook_clientconnect(self, context, clientconnect):
        if len(self.totalflowmap) == 0:
            self.copy_flow_map()
    
    def handle_hook_request(self, context, fl):
        referer = fl.request.headers.get_first("Referer")
        if referer is None:
            referer = ""            
        self.last_req_referer[referer] = fl.request.get_url()
        
        if self.content_mode:
            self.request_count += 1
            if InstrumentServer.DEBUG : print "Received request:", fl.request.get_url()
            if not self.request_exists(fl):
                if InstrumentServer.DEBUG : print "Error request:", fl.request.get_url()
                matchfl = self.find_approximate_match_request(fl.request)
                if matchfl != None:
                    self.process_approximate_match_request(matchfl, fl)
                else:
                    self.update_request_fail_total(fl)
                    if self.request_over_fail_limit(fl):
                        self.add_200_response(fl)
                    else:
                        self.add_404_response(fl)
        else:
            request_url = fl.request.get_url().strip()
            
            if self.normalize_url(request_url) == self.normalize_url(self.content_mode_url):
                if InstrumentServer.DEBUG : 
                    print "Found nocontent mode url: ", request_url, self.content_mode_url
                self.content_mode_url = None
                self.content_mode = True
            else:
                if InstrumentServer.DEBUG : 
                    print "Received request url " + fl.request.get_url() + " does not match " + \
                    self.content_mode_url 
                
            #we send a 204 in both cases so that the matched request still exists in the flow map
            self.replace_with_204_flow(fl)
            
        
    def handle_hook_response(self, context, fl):
        if self.content_mode:            
            head = fl.response.headers.get(InstrumentServer.GENERATED_HEADER)
            if head == None:
                self.complete_request_count += 1
                self.update_timestamp(fl)
            else:
                if InstrumentServer.DEBUG : 
                    print "Found Clickminer generated response."
#        else:
#            flcp = self.flow_204.copy()
#            fl.response = flcp.response.copy()
            
    def run(self):
        self.serve_forever()
    
    def read_all(self, rreqfile):
        buf = ""
        while True:
            buf += rreqfile.read(1)
            if buf.endswith("\n\n"): break
        
        return buf
    
    def handle_connection(self, request, client_address):
        if InstrumentServer.DEBUG: print "Execute handle_connection"
        
        try:
            rreqfile = request.makefile('r', -1)
            wreqfile = request.makefile('w', -1)
                        
            command = json.loads(self.read_all(rreqfile).strip())
            if InstrumentServer.DEBUG:
                print "Received command", command
              
            if command["cmd"] == InstrumentServer.MIN_REQ:
                self.handle_cmd_min_request(wreqfile)
            elif command["cmd"] == InstrumentServer.PRINT_REQS:        
                self.handle_cmd_print_requests(wreqfile)
            elif command["cmd"] == InstrumentServer.RECV_REQ_COUNT:
                self.handle_cmd_recv_req_count(wreqfile)
            elif command["cmd"] == InstrumentServer.CMPLT_REQ_COUNT:
                self.handle_cmd_cmplt_req_count(wreqfile)
            elif command["cmd"] == InstrumentServer.SET_TS:
                self.handle_cmd_set_ts(wreqfile, command["args"])
            elif command["cmd"] ==  InstrumentServer.POS_REQ:
                self.handle_cmd_pos_request(wreqfile, True)
            elif command["cmd"] ==  InstrumentServer.NEXT_POS_REQ:
                self.handle_cmd_pos_request(wreqfile)
            elif command["cmd"] ==  InstrumentServer.GET_MODE:
                self.handle_cmd_get_mode(wreqfile)
            elif command["cmd"] ==  InstrumentServer.SET_MODE_CONTENT:
                self.handle_cmd_set_mode_content(wreqfile)
            elif command["cmd"] == InstrumentServer.SET_MODE_NOCONTENT:
                self.handle_cmd_set_mode_nocontent(wreqfile, command["args"])
            elif command["cmd"] == InstrumentServer.SET_REQ_CHECK_LIMIT:
                self.handle_cmd_set_req_check_limit(wreqfile, command["args"])
            elif command["cmd"] == InstrumentServer.GET_REQ_CHECK_LIMIT:
                self.handle_cmd_get_req_check_limit(wreqfile)
            elif command["cmd"] == InstrumentServer.SET_FILTERED_RESP_TYPE:
                self.handle_cmd_set_filtered_resp_type(wreqfile, command["args"])
            elif command["cmd"] == InstrumentServer.REM_FILTERED_RESP_TYPE:
                self.handle_cmd_rem_filtered_resp_type(wreqfile, command["args"])
            elif command["cmd"] == InstrumentServer.GET_LAST_REQ_REFERER:
                self.handle_cmd_get_last_req_referer(wreqfile, command["args"])
            else :
                if InstrumentServer.DEBUG:
                    print "Received invalid command", command
                wreqfile.write(InstrumentServer.RESP_ERROR + ": Unrecognized command.")
    
            request.close()            
            rreqfile.close()
            wreqfile.flush()
            wreqfile.close()
        except Exception, e:
            if InstrumentServer.DEBUG:
                print e
                

    def handle_cmd_set_filtered_resp_type(self, wreqfile, args):
        if len(args) > 0:
            self.filtered_resp_types.extend(args)
            cmdresp = self.prepare_cmd_response(InstrumentServer.RESP_OK, 
                                                "Added " + str(len(args)) + " mime types to the filtered list.")
        else:
            cmdresp = self.prepare_cmd_response(InstrumentServer.RESP_OK, 
                                                "No mime types to add.")
        wreqfile.write(cmdresp)
    
    def handle_cmd_rem_filtered_resp_type(self, wreqfile, args):
        count = 0
        if len(args) > 0:
            for arg in args:
                if arg in self.filtered_resp_types:
                    self.filtered_resp_types.remove(arg)
                    count += 1
            
            cmdresp = self.prepare_cmd_response(InstrumentServer.RESP_OK, 
                                                "Removed " + str(count) + " mime type(s) from filter.")
        else:
            del self.filtered_resp_types[:]
            cmdresp = self.prepare_cmd_response(InstrumentServer.RESP_OK, 
                                                "Removed all mime types from filter.")
        wreqfile.write(cmdresp)
                
    def handle_cmd_get_last_req_referer(self, wreqfile, args):
        if InstrumentServer.DEBUG:
            print "Received command", InstrumentServer.GET_LAST_REQ_REFERER 
        if len(args) > 0:
            referer = args[0]
        else:
            referer = ""
          
        if self.last_req_referer.has_key(referer):
            cmdresp = self.prepare_cmd_response(InstrumentServer.RESP_OK, 
                                                data = [{"url": self.last_req_referer[referer]}])
        else:
            cmdresp = self.prepare_cmd_response(InstrumentServer.RESP_OK, 
                                                "No request received with the supplied referer.")     
        wreqfile.write(cmdresp)
        
                
                
    def handle_cmd_set_req_check_limit(self, wreqfile, args):
        if InstrumentServer.DEBUG:
            print "Received command", InstrumentServer.SET_REQ_CHECK_LIMIT       
        if len(args) > 0:
            try:
                limit = int(args[0])
                if limit < 0:
                    limit = 0
                if InstrumentServer.DEBUG:
                    print "Setting request check limit to", limit
                self.request_check_limit = limit
                cmdresp = self.prepare_cmd_response(InstrumentServer.RESP_OK)
            except ValueError:
                if InstrumentServer.DEBUG:
                    print "Limit argument", args[0], "is not an integer."
                cmdresp = self.prepare_cmd_response(InstrumentServer.RESP_ERROR, 
                                                "Argument must be an integer.")
        else:
            cmdresp = self.prepare_cmd_response(InstrumentServer.RESP_ERROR, 
                                                "Required argument missing.")
        wreqfile.write(cmdresp)
            
    def handle_cmd_get_req_check_limit(self, wreqfile):
        if InstrumentServer.DEBUG:
            print "Received command", InstrumentServer.GET_REQ_CHECK_LIMIT
        wreqfile.write(self.prepare_cmd_response(InstrumentServer.RESP_OK, 
                                            data = [{"limit": self.request_check_limit}]))
                       
    def handle_cmd_get_mode(self, wreqfile):
        if InstrumentServer.DEBUG:
            print "Received command", InstrumentServer.GET_MODE
        if self.content_mode:
            resp = {"mode": "content"}
        else:
            resp = {"mode": "nocontent"}
        wreqfile.write(self.prepare_cmd_response(InstrumentServer.RESP_OK, data = [resp]))
        
    def handle_cmd_set_mode_nocontent(self, wreqfile, args):
        if InstrumentServer.DEBUG:
            print "Received command", InstrumentServer.SET_MODE_NOCONTENT
        if len(args) > 0:
            if InstrumentServer.DEBUG:
                print "Setting match url to", args[0]
            self.content_mode_url = args[0]
            self.content_mode = False
            cmdresp = self.prepare_cmd_response(InstrumentServer.RESP_OK)
        else:
            cmdresp = self.prepare_cmd_response(InstrumentServer.RESP_ERROR, 
                                                "Required argument missing.")
        wreqfile.write(cmdresp)
    
    def handle_cmd_set_mode_content(self, wreqfile):
        if InstrumentServer.DEBUG:
            print "Received command", InstrumentServer.SET_MODE_CONTENT
        self.content_mode_url = None
        self.content_mode = True
        wreqfile.write(self.prepare_cmd_response(InstrumentServer.RESP_OK))
                   
    def handle_cmd_set_ts(self, wreqfile, args):
        if InstrumentServer.DEBUG:
            print "Received command", InstrumentServer.SET_TS
        if len(args) > 0:
            new_ts = float(args[0])
            if new_ts > 0.0:
                self.ts = new_ts
                cmdresp = self.prepare_cmd_response(InstrumentServer.RESP_OK)
            else:
                cmdresp = self.prepare_cmd_response(InstrumentServer.RESP_ERROR, 
                                                    "Argument value must be a positive number.")                
        else:
            cmdresp = self.prepare_cmd_response(InstrumentServer.RESP_ERROR, 
                                                "Required argument missing.")             
        wreqfile.write(cmdresp)
        
    # returns the number of request served with matching responses            
    def handle_cmd_cmplt_req_count(self, wreqfile):
        if InstrumentServer.DEBUG:
            print "Received command", InstrumentServer.CMPLT_REQ_COUNT
        wreqfile.write(self.prepare_cmd_response(InstrumentServer.RESP_OK, 
                                                 data = [{"count": self.complete_request_count}]))
    
    # returns the number of requests received by the proxy    
    def handle_cmd_recv_req_count(self, wreqfile):
        if InstrumentServer.DEBUG:
            print "Received command", InstrumentServer.RECV_REQ_COUNT
        wreqfile.write(self.prepare_cmd_response(InstrumentServer.RESP_OK, 
                                                 data = [{"count": self.request_count}]))
        
    # returns the representation of the requests stored for server playback    
    def handle_cmd_print_requests(self, wreqfile):
        if InstrumentServer.DEBUG:
            print "Received command", InstrumentServer.PRINT_REQS
        if self.master.server_playback != None:
            retval = self.print_requests()
            cmdresp = self.prepare_cmd_response(InstrumentServer.RESP_OK, data = [retval])
        else:
            cmdresp = self.prepare_cmd_response(InstrumentServer.RESP_ERROR, 
                "Server not in replay mode.")
        wreqfile.write(cmdresp)       
        
    def handle_cmd_min_request(self, wreqfile):
        if InstrumentServer.DEBUG:
            print "Received command ", InstrumentServer.MIN_REQ
            
        min_fl = self.find_min_flow()
        
        if min_fl != None:
            if InstrumentServer.DEBUG:
                print "Min request:", min_fl.request.timestamp_start, \
                       min_fl.request.method, min_fl.request.get_url()
                    
            cmdresp = self.prepare_cmd_response(InstrumentServer.RESP_OK, 
                                                data = [self.prepare_request_state(min_fl)])
        else:
            if InstrumentServer.DEBUG: print "Min request is None."
            cmdresp = self.prepare_cmd_response(InstrumentServer.RESP_OK, 
                                                "Min request is None.")   
        wreqfile.write(cmdresp)
            
    def handle_cmd_pos_request(self, wreqfile, regen_list=False):
        if InstrumentServer.DEBUG:
            if regen_list:
                print "Received command", InstrumentServer.POS_REQ
            else:
                print "Received command", InstrumentServer.NEXT_POS_REQ
                
        if regen_list:
            self.pos_req_list = self.generate_pos_requests(self.interleaving_window)
                              
        #Sometimes it seems (at least at Google News) that redirect url is replaced
        #in the DOM with the url that is the result of the redirect so we might 
        #want to check the redirect result url just in case.
        if (not regen_list and self.last_pos_req is not None and 
            self.last_pos_req.response.code in [http_status.MOVED_PERMANENTLY, 
                                                http_status.FOUND, http_status.SEE_OTHER]):
            window = self.find_flows_time_window(start_ts=self.last_pos_req.request.timestamp_start)
            loc_url = self.last_pos_req.response.headers.get_first("Location")
            
            if InstrumentServer.DEBUG:
                print "Looking for redirect result request with url", loc_url, \
                       "and a timestamp greater than", self.last_pos_req.request.timestamp_start
            
            for pos_fl in window:
                if pos_fl.request.get_url() == loc_url:
                    outlist = [pos_fl]
                    self.filter_pos_requests(outlist)
                    if(len(outlist) == 1):
                        if InstrumentServer.DEBUG:
                            print "Found redirect result request."
                        self.last_pos_req = pos_fl
                        wreqfile.write(self.prepare_cmd_response(InstrumentServer.RESP_OK, 
                                                                 data = [self.prepare_request_state(pos_fl)]))
                        return
                    else:
                        if InstrumentServer.DEBUG:
                            print "Found redirect result request, but request was filtered."
                        break
                    
        while True:
            try:
                #make sure the request is still available in the flow map
                fl = self.pos_req_list.pop(0)
                while not self.request_exists(fl) or self.request_over_check_limit(fl):
                    fl = self.pos_req_list.pop(0)
                
                if InstrumentServer.DEBUG:
                    print "Pos request:", fl.request.timestamp_start, \
                           fl.request.method, fl.request.get_url()
                        
                self.last_pos_req = fl
                self.update_request_check_total(fl)
                wreqfile.write(self.prepare_cmd_response(InstrumentServer.RESP_OK,
                                                         data = [self.prepare_request_state(fl)]))
                break
            except UnicodeError:
                self.remove_flow(fl)
                if InstrumentServer.DEBUG:
                    traceback.print_exc(file=sys.stdout)
                    print "Unable to process request: ", fl.request.timestamp_start, \
                           fl.request.method, fl.request.get_url()
                    print "Skipping request."
            except IndexError:
                if InstrumentServer.DEBUG: print "No possible requests."
                wreqfile.write(self.prepare_cmd_response(InstrumentServer.RESP_OK, 
                                                                 "No possible requests."))
                break
            
    def request_exists(self, flow):
        hashval = self.master.server_playback._hash(flow)
        l = self.master.server_playback.fmap.get(hashval)
        return l != None and len(l) > 0
    
    def remove_flow(self, flow):
        hashval = self.master.server_playback._hash(flow)
        del self.master.server_playback.fmap[hashval]
        
    def add_flow(self, fl):
        hashval = self.master.server_playback._hash(fl)
        l = self.master.server_playback.fmap.setdefault(hashval, [])
        l.append(fl)
        
        if InstrumentServer.DEBUG:
            if self.request_exists(fl):
                print "Successfully added flow with hashval", hashval.encode('hex')
            else:
                print "Failed to add flow with hashval", hashval.encode('hex')
                
    def compute_num_requests_refered(self):
#        if InstrumentServer.DEBUG:
#            print "Starting compute_num_requests_refered"
        
        fls = self.find_flows_time_window()
        for fl in fls:
            referer = fl.request.headers.get_first("Referer")
            if referer is not None:
                if self.num_requests_refered.has_key(referer):
                    self.num_requests_refered[referer] += 1
                else:
                    self.num_requests_refered[referer] = 1
                    
#        if InstrumentServer.DEBUG:
#            for url, count in self.num_requests_refered.iteritems():
#                print "url:", url, "total_referees:", count
                
#            print "Ending compute_num_requests_refered"         
          
    def compute_req_referer_time_diff(self):
#        if InstrumentServer.DEBUG:
#            print "Starting compute_req_referer_time_diff"
        fls = self.find_flows_time_window()
        fls.reverse()
        for i in range(len(fls)):
            referer = fls[i].request.headers.get_first("Referer")
            delta = 0
            if referer is not None:
                found = False
                for j in range(i+1, len(fls)):
                    if fls[j].request.get_url() == referer:
                        delta = fls[i].request.timestamp_start - fls[j].response.timestamp_end
                        found = True
                        break
                # if a request has a referer but we can't find the referer request then
                # then set delta to -1 to show there was an error
                if not found: delta = -1
                    
            self.req_referer_time_diff[self.ext_hash(fls[i])] = float(delta)
            if InstrumentServer.DEBUG:
                print "Request:", fls[i].request.get_url(), fls[i].request.timestamp_start, \
                       " has a referer delay of", float(delta)
                
#        if InstrumentServer.DEBUG:
#            print "Ending compute_req_referer_time_diff"
                
    def copy_flow_map(self):
        for key in self.master.server_playback.fmap.keys():
            flowlist = self.master.server_playback.fmap[key]
            self.totalflowmap[key] = list()
            for fl in flowlist:
                self.totalflowmap[key].append(fl.copy())
                
    def update_timestamp(self, fl):
        requrl = fl.request.get_url()
        if requrl in self.skip_ts_update_list:
            self.skip_ts_update_list.remove(requrl)
            if InstrumentServer.DEBUG: 
                print "Request url", requrl, \
                    "exists in skip_ts_update_list.  Skipping ts update."
        elif fl.response.timestamp_start > self.ts:
            self.ts = fl.response.timestamp_start
            if InstrumentServer.DEBUG: print "Updated server timestamp to", self.ts
            
    def process_approximate_match_request(self, matchfl, fl):
        fl.request._load_state(matchfl.request._get_state())
        
        # We want to skip updating the server timestamp as we can not be sure
        # when the match occurs within the session.
        # For instance, if the matched request is at the end of the session then we 
        # could end up skipping alot of request we would like to process.
        self.skip_ts_update_list.append(matchfl.request.get_url());
        
    def update_request_fail_total(self, fl):
        url = fl.request.get_url()
        if self.request_fail_count.has_key(url):
            self.request_fail_count[url] += 1
        else:
            self.request_fail_count[url] = 1
            
    def request_over_fail_limit(self,fl):
        url = fl.request.get_url()
        if self.request_fail_count.has_key(url):
            return self.request_fail_count[url] > self.request_fail_limit
        return False
    
    def update_request_check_total(self, fl):
        hashval = self.ext_hash(fl)
        if self.request_check_count.has_key(hashval):
            self.request_check_count[hashval] += 1
        else:
            self.request_check_count[hashval] = 1
            
        if InstrumentServer.DEBUG: 
            print "Updated request check to total for request with url", \
                fl.request.get_url(), "and timestamp", fl.request.timestamp_start, \
                "to", self.request_check_count[hashval]
            
    def request_over_check_limit(self, fl):
        hashval = self.ext_hash(fl)
        return (self.request_check_limit > 0 and 
            self.request_check_count.has_key(hashval) and 
            self.request_check_count[hashval] >= self.request_check_limit)
    
    def find_approximate_match_request(self, sendreq):
        print "Finding approx. match for request:", sendreq.get_url()
        
        matchcands = list()
        flowmap = self.master.server_playback.fmap     
        for key in flowmap.keys():
            for fl in flowmap[key]:
                posreq = fl.request
                
                path_simil_val = 0
                param_intersec_val = 0
                param_values_val = 0
                
                
                #if InstrumentServer.DEBUG: print "Testing request: " + posreq.get_url()
                                
                #A match request should have the same method and host
                if sendreq.method == posreq.method and sendreq.host == posreq.host:
                    
                    if InstrumentServer.DEBUG: print "Possible match for method and host."
                    
                    posreqpath = urlparse.urlparse(posreq.get_url()).path
                    sendreqpath = urlparse.urlparse(sendreq.get_url()).path
                    
                    
                    if posreqpath[0] == "/":
                        posreqpath = posreqpath[1:]
                    
                    if sendreqpath[0] == "/":
                        sendreqpath = sendreqpath[1:]
                        
                    posreqpathparts = posreqpath.split("/")
                    sendreqpathparts =  sendreqpath.split("/")
                    
                    # if the two paths have the same number of elements then continue
                    if len(posreqpathparts) == len(sendreqpathparts):
                        
                        if InstrumentServer.DEBUG: print "Possible match for path length."
                        
                        samepathcount = 0
                        for i in range(len(sendreqpathparts)):
                            if sendreqpathparts[i] != posreqpathparts[i]:
                                break
                            samepathcount += 1
                        
                        if len(sendreqpathparts) < 1:
                            path_simil_val = 0.0
                        else:
                            path_simil_val = float(samepathcount)/float(len(sendreqpathparts))
                            
                        if InstrumentServer.DEBUG: 
                            print "Path similarity ratio:", path_simil_val
                            
                        #if the path similarity ratio is greater than the threshhold then continue    
                        if path_simil_val > self.path_simil_threshhold:
                            
                            if InstrumentServer.DEBUG: 
                                    print "Possible match for path similarity."
                            
                            #extract the params and their values
                            if sendreq.method.upper() == "POST":
                                sendreqparams = self.extract_request_parameters(sendreq, False)
                                posreqparams = self.extract_request_parameters(posreq, False)
                            elif sendreq.method.upper() == "GET":
                                sendreqparams = self.extract_request_parameters(sendreq, True)
                                posreqparams = self.extract_request_parameters(posreq, True)
                            
                            if InstrumentServer.DEBUG: 
                                print "Send Request Params:", sendreqparams
                                print "Possible Request Params:", posreqparams
                            
                            #if the param intersection ratio is greater than the threshhold then continue    
                            paramsintersec = set(sendreqparams.keys()) & set(posreqparams.keys())
                            if InstrumentServer.DEBUG: print "Param intersection:", paramsintersec
                            
                            if len(sendreqparams.keys()) < 1:
                                param_intersec_val = 0.0
                            else:
                                param_intersec_val = float(len(paramsintersec)) / float(len(sendreqparams.keys()))
                            
                            if InstrumentServer.DEBUG: 
                                print "Param intersection ratio:", param_intersec_val
                            
                            if param_intersec_val >= self.param_intersec_threshhold:
                                if InstrumentServer.DEBUG: 
                                    print "Possible match for parameter intersection."
                                
                                samevaluecount = 0;
                                for param in paramsintersec:
                                    if sendreqparams[param] == posreqparams[param]:
                                        samevaluecount += 1;
                                
                                if len(paramsintersec) < 1:
                                    param_values_val = 0.0
                                else:
                                    param_values_val = float(samevaluecount) / float(len(paramsintersec))
                                
                                if InstrumentServer.DEBUG: 
                                    print "Param values ratio:", param_values_val
                                            
                                #if the param values ratio of the intersection is greater than
                                #the threshhold then return posreq as a match
                                if param_values_val >= self.param_values_threshold:
                                    if InstrumentServer.DEBUG: print "Found possible matching request", \
                                                                      fl.request.get_url()
                                    
                                    # we use the inverse distance so we can use the max function to find the smallest temporal distance
                                    inv_temporal_distance = (1 / math.fabs(self.ts - fl.request.timestamp_start))
                                    matchcands.append((path_simil_val, param_intersec_val, param_values_val,
                                                       inv_temporal_distance, fl))
                                    
        if len(matchcands) < 1:
            return None
        else:
            #return the match with the largest path_simil_val then param_intersec_val and lastly param_values_val
            bestfl = max(matchcands, key=itemgetter(0,1,2,3))[4]
            if InstrumentServer.DEBUG:
                print "Match for", sendreq.get_url()
                print "is", bestfl.request.get_url()
            return bestfl
            
                        
    def extract_request_parameters(self, request, isget=True):
        params = dict()
        if isget:
            query = urlparse.urlparse(request.get_url()).query
        else:
            query = urlparse.urlparse(request.content).query
            
        if query and query != "":
            paramlist = utils.urldecode(query)
            for k, v in paramlist:
                params[k] = v
                
        return params
    
    def matches_web_api(self, fl):
        requesturl = fl.request.get_url().strip()
        for apiurl in InstrumentServer.WEB_API_URLS:
            if requesturl.startswith(apiurl):
                return True
        return False
    
    #deal with special response codes like some 3XX
    #remove all requests not in the original saved flows
    #remove all requests with 4XX or 5XX response codes
    #remove all 204 No Content requests
    #remove all XMLHttpRequests
    #remove all X-Clickminer-Generated responses
    #See http://en.wikipedia.org/wiki/List_of_HTTP_status_codes
    #See http://en.wikipedia.org/wiki/List_of_HTTP_header_fields
    def filter_pos_requests(self, fls):
        flsorder = sorted(fls, key=attrgetter('request.timestamp_start'))
        for fl in fls:
            if self.ext_hash(fl) not in self.req_referer_time_diff:
                if InstrumentServer.DEBUG:
                    print "Filtered request not in the saved flows.", fl.request.get_url()
                if fl in fls:
                    fls.remove(fl)
                continue
            
            
            if self.matches_web_api(fl):
                if InstrumentServer.DEBUG:
                    print "Filtered request for a known web api", fl.request.get_url()
                if fl in fls:
                    fls.remove(fl)
                continue
                
            xrw_val = fl.request.headers.get_first("X-Requested-With")
            if xrw_val is not None and xrw_val == "XMLHttpRequest":
                if fl in fls:
                    fls.remove(fl)
                if InstrumentServer.DEBUG:
                    print "Filtered XMLHttpRequest request."
                continue
            
 
            resp = fl.response
            resptype = resp.headers.get_first("Content-Type")
            if resptype is not None and resptype in self.filtered_resp_types:
                if fl in fls:
                    fls.remove(fl)
                if InstrumentServer.DEBUG:
                    print "Filtered request with response of type", resptype
                continue
            
            
            cm_val = resp.headers.get_first(InstrumentServer.GENERATED_HEADER)
            if cm_val is not None:
                if fl in fls:
                    fls.remove(fl)
                if InstrumentServer.DEBUG:
                    print "Filtered Clickminer generated request."
                continue
            
            #for XMLHttpRequests we still need to filter out requests if the 
            #response to the request is a redirect
            if resp.code in [http_status.MOVED_PERMANENTLY,
                             http_status.FOUND, http_status.SEE_OTHER]:
                loc_url = resp.headers.get_first("Location")
                for pos_fl in flsorder:
                    if (pos_fl.request.timestamp_start > resp.timestamp_start and 
                        pos_fl.request.get_url() == loc_url):
                        if pos_fl in fls:
                            fls.remove(pos_fl)
                        
                        if pos_fl in flsorder:
                            flsorder.remove(pos_fl)
                        if InstrumentServer.DEBUG:
                            print "Filtered request due to a request with a response code of", resp.code, "."
                        break
                    
            elif resp.code == http_status.TEMPORARY_REDIRECT:
                loc_url = resp.headers.get_first("Location")
                orig_method = fl.request.method
                for pos_fl in flsorder:
                    if (pos_fl.request.timestamp_start > resp.timestamp_start and 
                        pos_fl.request.method == orig_method and 
                        pos_fl.request.get_url() == loc_url):
                        if pos_fl in fls:
                            fls.remove(pos_fl)
                            
                        if pos_fl in flsorder:
                            flsorder.remove(pos_fl)
                        
                        
                        if InstrumentServer.DEBUG:
                            print "Filtered request due to a request with a response code of", resp.code, "."
                        break
                    
            elif resp.code >= 400 and resp.code <= 599:
                if fl in fls:
                    fls.remove(fl)
                if InstrumentServer.DEBUG:
                    print "Filtered request with a response code of", resp.code, "."
                
            elif resp.code == http_status.NO_CONTENT:
                if fl in fls:
                    fls.remove(fl)
                else:
                    if InstrumentServer.DEBUG:
                        print "This flow should be in the list.  'How did this happen."
                        print self.prepare_request_state(fl)
                if InstrumentServer.DEBUG:
                    print "Filtered request with a response code of", resp.code, "."
                
                    
    # delay is measured in seconds
    def generate_pos_requests(self, il_size = 20):
        il_window = self.find_interleaving_size_window(il_size)
        temp = self.find_flows_time_window(end_ts=self.ts)
        for fl in temp:
            if fl not in il_window: il_window.append(fl)
                
        temp = self.find_flows_time_window(start_ts=self.ts)
        for fl in temp:
            if fl not in il_window: il_window.append(fl)
    
#        il_window = self.find_interleaving_time_window(delay)
#        il_window.extend(self.find_skipped_flows(delay))
#        il_window.extend(self.find_flows_time_window(start_ts=(self.ts + delay)))
        self.filter_pos_requests(il_window)
        return il_window
    
    # bounds (start_ts, end_ts]
    # returns list of flows in chronological order
    def find_flows_time_window(self, start_ts=0.0, end_ts=sys.float_info.max):
        fls = list()
        if self.master != None and self.master.server_playback != None:
            flowmap = self.master.server_playback.fmap    
            for key in flowmap.keys():
                for fl in flowmap[key]:
                    if (fl.request.timestamp_start > start_ts and 
                        fl.request.timestamp_start <= end_ts):
                        fls.append(fl)
                        
        if len(fls) > 0:
            return sorted(fls, key=attrgetter('request.timestamp_start'))
        else:
            return fls
    
    # returns the window the window of flows of up to size n 
    # from the proxy's current timestamp.  If forward is true 
    # then the the proxy timestamp is used as the beginning of
    # the window.  If false, it is uses as the end.
    # returns list of flows in chronological order    
    def find_flows_size_window(self, n, forward=True):
        retval = list()
        if forward:
            fls = self.find_flows_time_window(start_ts=self.ts)
        else:
            fls = self.find_flows_time_window(end_ts=self.ts)
            
        index = 0
        while len(retval) <= n and index < len(fls):
            retval.append(fls[index])
            index +=1
            
        return retval
             

    def find_skipped_flows(self, delay):
        return self.find_flows_time_window(end_ts=(self.ts - delay))
    
    
    def find_interleaving_size_window(self, n):
        retval = self.find_flows_size_window(n)
        retval.extend(self.find_flows_size_window(n, False))
        return retval
                      
    
    # delay is measured in seconds
    # flows in (self.ts - delay, self.ts + delay]    
    def find_interleaving_time_window(self, delay):
        window = self.find_flows_time_window(start_ts=(self.ts - delay),
                                              end_ts=(self.ts + delay))            
        return window

    # delay is measured in seconds
    # min of (self.ts - delay, sys.float_info.max]      
    def find_min_flow(self, delay = 0):
        fls = self.find_flows_time_window(start_ts=(self.ts - delay))
        if len(fls) > 0:
            return fls[0]
        else:
            return None
        
    def prepare_request_state(self, fl):
        request_state = fl.request._get_state()
        #add url for convenience
        request_state["url"] = fl.request.get_url()
            
        #to be used by the browser in its determination of if the request
        #represents a user interaction
        try:
            request_state["delay_from_referer"] = self.req_referer_time_diff[self.ext_hash(fl)]
        except Exception, e:
            print "Request: ", fl.request._get_state(), "\nResponse: ", fl.response._get_state()
            raise e
        
        if request_state["url"] in self.num_requests_refered:
            request_state["num_requests_refered"] = self.num_requests_refered[request_state["url"]]
        else:
            request_state["num_requests_refered"] = 0
            
        request_state["response_content_type"] = fl.response.headers.get_first("Content-Type")
        
        return request_state
    
    def prepare_cmd_response(self, status, msg=None, data=[]):
        response = dict()
        response['status'] = status
        response['msg'] = msg
        response['data'] = data
        return json.dumps(response)
    
    def request_to_json(self, fl):        
        return json.dumps(self.prepare_request_state(fl))
        
    def print_requests(self):    
        retval = dict()
        counter = 0
        flowmap = self.master.server_playback.fmap    
        for key in flowmap.keys():
            for fl in flowmap[key]:
                retval["Request" + str(counter)] = self.prepare_request_state(fl)
                counter += 1
        return json.dumps(retval)
    
    def print_request_in_order(self):
        fls = self.find_flows_time_window()
        for i in range(len(fls)):
            print "Timestamp:", fls[i].request.timestamp_start, "Url:", \
                fls[i].request.get_url(), "Referer:", fls[i].request.headers.get_first("Referer")
    
    def normalize_url(self, url):
        if url[len(url) - 1] == "/":
            return urllib.quote_plus(url[:len(url)-1])
        else:
            return urllib.quote_plus(url)
        
    def ext_hash(self, fl):
        #we add the timestamp to the hash to handle multiple 
        #of the same request at different times
        return self.master.server_playback._hash(fl) + str(fl.request.timestamp_start)
    
    def replace_with_204_flow(self, fl):
#        resp = flow.Response(fl.request, fl.request.httpversion, http_status.NO_CONTENT, 
#                             http_status.RESPONSES[http_status.NO_CONTENT], headers, 
#                             "", None, time.time(), time.time())
#        fl.response = resp
#        self.add_flow(fl)
#        self.replace_response(http_status.NO_CONTENT, fl)    
        flcp = self.flow_204.copy()
        flcp.response.headers.add(InstrumentServer.GENERATED_HEADER, time.time())
        fl.request._load_state(flcp.request._get_state())
        fl.response = flcp.response.copy()
        self.add_flow(flcp)
        
    def add_404_response(self, fl):
#        resp = flow.Response(fl.request, fl.request.httpversion, http_status.NOT_FOUND, 
#                             http_status.RESPONSES[http_status.NOT_FOUND], odict.ODictCaseless(), 
#                             "", None, time.time(), time.time())
#        fl.response = resp
#        self.add_flow(fl)
        self.replace_response(http_status.NOT_FOUND, fl)
        
    def replace_response(self, status, fl, content="", content_type="text/plain"):
        headers = odict.ODictCaseless()
        headers.add(InstrumentServer.GENERATED_HEADER, time.time())
        headers.add("Server", "Clickminer-proxy")
        headers.add("Content-Length", len(content))
        headers.add("Content-Type", content_type)
        headers.add("Connection", "close")
        headers.add("Date", time.strftime("%a, %d %b %Y %H:%M:%S GMT", time.gmtime()))
        
        resp = flow.Response(fl.request, fl.request.httpversion, status, 
                             http_status.RESPONSES[status], headers, 
                             content, None, time.time(), time.time())
        fl.response = resp
        self.add_flow(fl)
        
    def add_200_response(self, fl):
        if not mimetypes.inited:
            mimetypes.init()
        
        path_comps = fl.request.get_path_components()
        ext = None
        if len(path_comps) > 0:
            parts = os.path.splitext(path_comps.pop())
            if parts[0] != "":
                ext = parts[1]

        types = None
        accept_val = fl.request.headers.get_first("Accept")
        if accept_val is not None:
            types = self.parse_accept_header(accept_val)
            if ext in mimetypes.types_map and mimetypes.types_map[ext] not in types:
                types.insert(0, mimetypes.types_map[ext])
                        
        content_type, content = self.generate_dummy_content(types, ext.lstrip(".") if ext is not None else None )
        if InstrumentServer.DEBUG:
            print content_type, content
        
        self.replace_response(http_status.OK, fl, content, content_type)
        
            
    def generate_dummy_content(self, accept_types, ext=None):
        for mimetype in accept_types:
            type_parts = mimetype.split("/")
            val = None
            if type_parts[0] == "image":
                if type_parts[1] == "*" or ext is None:
                    val = self.generate_dummy_image()
                else:
                    try:
                        val = self.generate_dummy_image(ext)
                    except:
                        try:
                            val = self.generate_dummy_image(type_parts[1])
                        except:
                            val = self.generate_dummy_image()
                            mimetype = "image/png"
            if type_parts[0] == "text" or type_parts[0] == "*":
                val = ""
            if val is not None:
                return (mimetype, val)
        return ("text/plain", "")
               
    def parse_accept_header(self, header_val):
        out = []
        parts = header_val.split(";")
        for part in parts:
            subparts = part.split(",")
            for subpart in subparts:
                if subpart.find("=") == -1 and subpart not in out:
                    out.append(subpart)
        return out
        
    def generate_dummy_image(self, img_format="png"):
        out = StringIO()
        im = Image.fromstring("L", (1,1), "\xff")
        im.save(out, img_format)
        retval = out.getvalue()
        out.close()
        return retval
        
        
    
    