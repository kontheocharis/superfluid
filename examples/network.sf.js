var { Buffer } = require('node:buffer');
var prompt = require('prompt-sync')();
var id = (v00) => (a5) => a5;
var if_then_else = (A12) => (b13) => (t14) => (f15) => (b13) ? ((t14)(["tt"])) : ((f15)(["tt"]));
var js_two = (1) + (1);
var js_four = ((1) + (1)) * ((1) + (1));
var js_six = (((1) + (1)) * ((1) + (1))) + ((1) + (1));
var js_eight = (((1) + (1)) * ((1) + (1))) * (((1) + (1)) * ((1) + (1)));
var debug_print = (v11) => (a120) => (() => ((console).log)(a120));
var sub = (m167) => (n168) => ((n168) === (0)) ? (m167) : (((m167) === (0)) ? (0) : (((sub)((m167) - (1)))((n168) - (1))));
var find = (v4747) => (p266) => (xs267) => (() => {
  var l_p_379 = xs267;
  return (((l_p_379).length) === (0)) ? (null) : (((p266)((l_p_379)[0])) ? ((l_p_379)[0]) : ((((find)(null))(p266))((l_p_379).slice(1, (l_p_379).length))));
})();
var Word = null;
var Byte = null;
var OWN_PORT = 3096;
var max_fin = (v190190) => (x24) => (y25) => ((x24) === (0)) ? (y25) : (((y25) === (0)) ? (x24) : ((1) + ((((max_fin)(null))((x24) - (1)))((y25) - (1)))));
var handle_packet = (p35) => (() => {
  switch ((p35)[0]) {
    case "mk_udp_packet": return ((((p35)[(1) + (0)]) % ((1) + (1))) === (0)) ? ((() => {
      var new_p44 = ["mk_udp_packet", OWN_PORT, (p35)[(1) + ((1) + (0))], (p35)[(1) + ((1) + ((1) + (0)))], (p35)[(1) + ((1) + ((1) + ((1) + (0))))], (p35)[(1) + ((1) + ((1) + ((1) + ((1) + (0)))))]];
      return new_p44;
    })()) : (null);
  }
})();
var repeat = (v202202) => (f52) => (b53) => ((f52) === (0)) ? (["bnil", null]) : (["bcons", null, (f52) - (1), b53, (((repeat)(null))((f52) - (1)))(b53)]);
var io_mapM_ = (v210210) => (f67) => (xs68) => (() => {
  var l_p_379 = xs68;
  return (((l_p_379).length) === (0)) ? ((() => ["tt"])) : ((() => {
    var m75 = (() => (((_77) => (((io_mapM_)(null))(f67))((l_p_379).slice(1, (l_p_379).length)))(((f67)((l_p_379)[0]))()))());
    return m75;
  })());
})();
var list_range = (n80) => ((n80) === (0)) ? ([]) : ([(n80) - (1), ...((list_range)((n80) - (1)))]);
var main = (() => {
  var packet_size85 = 20000;
  var contents86 = (((repeat)(65536))(packet_size85))(42);
  var test_packet87 = ["mk_udp_packet", 2, 3, packet_size85, 5, contents86];
  return (((io_mapM_)(null))((i88) => (() => (((_90) => (() => {
    var result91 = (handle_packet)(test_packet87);
    return ((result91) === (null)) ? (((debug_print)(null))("No UDP packet!")) : ((() => {
      switch ((result91)[0]) {
        case "mk_udp_packet": return ((debug_print)(Word))((result91)[(1) + ((1) + ((1) + (0)))]);
      }
    })());
  })())((((debug_print)(null))(i88))()))())))((list_range)(200));
})();
(main)()