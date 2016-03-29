__clickminer-proxy__ implements ClickMiner's replay proxy.

Usage
-----

clickminer-proxy contains a script instrument_server.py to be used with mitmproxy.

To start clickminer-proxy once mitmproxy has been installed execute the following command:
mitmdump --norefresh -e -s instrument_server.py -k --keepserving -S <trace_flows>

Note:  The file <trace_flow> can either be recorded using mitmproxy or extracted
from a pcap file using mitmextract

Requirements
------------

* [Python](http://www.python.org) 2.7.x
* [mitmproxy](http://github.com/cortesi/mitmproxy) (53792a5)
* [netlib](http://github.com/cortesi/netlib) (7d18535)

Optional
--------
* [mitmextract](http://github.com/cjneasbi/mitmextract) (master)
