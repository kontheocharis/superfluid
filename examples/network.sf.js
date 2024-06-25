const { Buffer } = require('node:buffer');
const prompt = require('prompt-sync')();
const id = (A) => (a) => a;
const if_then_else = (A) => (b) => (t) => (f) => (b) ? ((t)(["tt"])) : ((f)(["tt"]));
const debug_print = (A) => (a) => (() => ((console).log)(a));
const sub = (m) => (n) => ((n) === (0)) ? (m) : (((m) === (0)) ? (0) : (((sub)((m) - (1)))((n) - (1))));
const find = (A) => (p) => (xs) => (((xs).length) === (0)) ? (null) : (((p)((xs)[0])) ? ((xs)[0]) : ((((find)(A))(p))((xs).slice(1, (xs).length))));
const Char = null;
const STRING = null;
const two = (1) + ((1) + (0));
const two_to_the_sixteen = (two) ** ((two) ** ((two) ** (two)));
const field_len = two_to_the_sixteen;
const byte_len = two_to_the_sixteen;
const Word = null;
const process_udp_packet = (p) => (() => {
  const js_two = (1) + (1);
  const js_four = (js_two) * (js_two);
  const js_six = (js_four) + (js_two);
  const js_eight = (js_four) * (js_four);
  const src_port = ((p).readUInt16BE)(0);
  const dst_port = ((p).readUInt16BE)(js_two);
  const len = ((p).readUInt16BE)(js_four);
  const checksum = ((p).readUInt16BE)(js_six);
  const contents = ((p).subarray)(js_eight, (js_eight) + (len));
  return (((Buffer.byteLength)(contents)) === (0)) ? (["error", Word, null, false]) : ((((contents)[0]) === (0)) ? ((((Buffer.byteLength)(((contents).subarray)(1, (Buffer.byteLength)(contents)))) === (0)) ? (["ok", Word, null, src_port]) : (["ok", Word, null, checksum])) : (["error", Word, null, false]));
})();
(main)()