const { Buffer } = require('node:buffer');
const prompt = require('prompt-sync')();
const id = (A) => (a) => a;
const if_then_else = (A) => (b) => (t) => (f) => (b) ? ((t)(["tt"])) : ((f)(["tt"]));
const debug_print = (A) => (a) => (() => ((console).log)(a));
const sub = (m) => (n) => ((n) === (0)) ? (m) : (((m) === (0)) ? (0) : (((sub)((m) - (1)))((n) - (1))));
const find = (A) => (p) => (xs) => (((xs).length) === (0)) ? (null) : (((p)((xs)[0])) ? ((xs)[0]) : ((((find)(A))(p))((xs).slice(1, (xs).length))));
const Char = null;
const STRING = null;
const ByteArray = null;
const USize = null;
const byte_array_len = (b) => (Buffer.byteLength)(b);
const FlatArray = (u) => (t) => null;
const usize_zero = 0;
const usize_one = 1;
const usize_add = (a) => (b) => (a) + (b);
const usize_sub = (a) => (b) => (a) - (b);
const is_usize_zero = (a) => (a) === (0);
const two = (1) + ((1) + (0));
const two_to_the_sixteen = (two) ** ((two) ** ((two) ** (two)));
const field_len = two_to_the_sixteen;
const byte_len = two_to_the_sixteen;
const process_udp_packet = (p) => (() => {
  switch ((p)[0]) {
    case "mk_udp_packet": return ((((((src_port) => (dst_port) => (len) => (checksum) => (contents) => (() => {
      const first_byte = (((contents).length) === (0)) ? (null) : ((contents)[0]);
      return ((first_byte) === (null)) ? (["error"]) : (((first_byte) === (0)) ? (["ok"]) : (["error"]));
    })())((p)[1]))((p)[2]))((p)[3]))((p)[4]))((p)[5]);
  }
})();
(main)()