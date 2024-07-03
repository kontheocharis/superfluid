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
var handle_packet = (seq22) => (p23) => (() => {
  var p_p_128 = p23;
  var len129 = ((p_p_128).readUInt16BE)(4);
  return (() => {
    var own_port30 = (((seq22) % ((1) + (1))) === (0)) ? (42) : (24);
    var new_p34 = (() => {
      var len_p_116 = len129;
      var total_len117 = (len_p_116) + (8);
      var b118 = (Buffer.allocUnsafe)(total_len117);
      var b_p_119 = (((b118).writeUInt16BE)(own_port30, 0), b118);
      var b_p__p_121 = (((b_p_119).writeUInt16BE)(((p_p_128).readUInt16BE)(2), 2), b_p_119);
      var b_p__p__p_122 = (((b_p__p_121).writeUInt16BE)(len_p_116, 4), b_p__p_121);
      var b_p__p__p__p_123 = (((b_p__p__p_122).writeUInt16BE)(((p_p_128).readUInt16BE)(6), 6), b_p__p__p_122);
      var b_p__p__p__p__p_124 = (((((p_p_128).subarray)(8, (8) + (len129))).copy)(b_p__p__p__p_123, 8, 0, len_p_116), b_p__p__p__p_123);
      return b_p__p__p__p__p_124;
    })();
    return new_p34;
  })();
})();
var repeat = (n38) => (b39) => ((n38) === (0)) ? ((Buffer.allocUnsafe)(0)) : ((() => {
  var xs_p_90 = ((repeat)((n38) - (1)))(b39);
  var old_len91 = (Buffer.byteLength)(xs_p_90);
  var new_len93 = (old_len91) + (1);
  var b95 = (Buffer.allocUnsafe)(new_len93);
  var b_p_96 = (((b95).writeUInt8)(b39, 0), b95);
  return (((xs_p_90).copy)(b_p_96, 1, 0, old_len91), b_p_96);
})());
var io_mapM_ = (v191191) => (f53) => (xs54) => (() => {
  var l_p_379 = xs54;
  return (((l_p_379).length) === (0)) ? ((() => ["tt"])) : ((() => {
    var m61 = (() => (((_63) => (((io_mapM_)(null))(f53))((l_p_379).slice(1, (l_p_379).length)))(((f53)((l_p_379)[0]))()))());
    return m61;
  })());
})();
var count_to = (n66) => ((n66) === (0)) ? ([]) : ([(n66) - (1), ...((count_to)((n66) - (1)))]);
var main = (() => {
  var packet_size71 = 20000;
  var contents72 = ((repeat)(packet_size71))(42);
  var test_packet73 = (() => {
    var len_p_116 = packet_size71;
    var total_len117 = (len_p_116) + (8);
    var b118 = (Buffer.allocUnsafe)(total_len117);
    var b_p_119 = (((b118).writeUInt16BE)(2, 0), b118);
    var b_p__p_121 = (((b_p_119).writeUInt16BE)(3, 2), b_p_119);
    var b_p__p__p_122 = (((b_p__p_121).writeUInt16BE)(len_p_116, 4), b_p__p_121);
    var b_p__p__p__p_123 = (((b_p__p__p_122).writeUInt16BE)(5, 6), b_p__p__p_122);
    var b_p__p__p__p__p_124 = (((contents72).copy)(b_p__p__p__p_123, 8, 0, len_p_116), b_p__p__p__p_123);
    return b_p__p__p__p__p_124;
  })();
  return (((io_mapM_)(null))((i74) => (() => (((_76) => (() => {
    var result77 = ((handle_packet)(i74))(test_packet73);
    return ((result77) === (null)) ? (((debug_print)(null))("No UDP packet!")) : (((debug_print)(null))(result77));
  })())((((debug_print)(null))(i74))()))())))((count_to)(2000));
})();
var word_to_big_endian_bytes = null;
var write_other_byte_vec = (v274274) => (v275275) => null;
(main)()