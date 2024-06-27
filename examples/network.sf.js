const { Buffer } = require('node:buffer');
const prompt = require('prompt-sync')();
const id = (A) => (a) => a;
const if_then_else = (A) => (b) => (t) => (f) => (b) ? ((t)(["tt"])) : ((f)(["tt"]));
const js_two = (1) + (1);
const js_four = ((1) + (1)) * ((1) + (1));
const js_six = (((1) + (1)) * ((1) + (1))) + ((1) + (1));
const js_eight = (((1) + (1)) * ((1) + (1))) * (((1) + (1)) * ((1) + (1)));
const debug_print = (A) => (a) => (() => ((console).log)(a));
const sub = (m) => (n) => ((n) === (0)) ? (m) : (((m) === (0)) ? (0) : (((sub)((m) - (1)))((n) - (1))));
const find = (A) => (p) => (xs) => (() => {
  const l_p_ = xs;
  return (((l_p_).length) === (0)) ? (null) : (((p)((l_p_)[0])) ? ((l_p_)[0]) : ((((find)(null))(p))((l_p_).slice(1, (l_p_).length))));
})();
const field_len = (2) ** (16);
const byte_len = (2) ** (16);
const Word = null;
const OWN_PORT = 4;
const handle_packet = (p) => (() => {
  const p_p_ = p;
  const len = ((p_p_).readUInt16BE)(4);
  const src_port = ((p_p_).readUInt16BE)(0);
  const dst_port = ((p_p_).readUInt16BE)(2);
  const checksum = ((p_p_).readUInt16BE)(6);
  const contents = ((p_p_).subarray)(8, (8) + (len));
  return (((src_port) % ((1) + (1))) === (0)) ? ((() => {
    const new_p = (() => {
      const len_p_ = len;
      const total_len = (len_p_) + (8);
      const b = (Buffer.allocUnsafe)(total_len);
      const b_p_ = (((b).writeUInt16BE)(OWN_PORT, 0), b);
      const b_p__p_ = (((b_p_).writeUInt16BE)(dst_port, 2), b_p_);
      const b_p__p__p_ = (((b_p__p_).writeUInt16BE)(len_p_, 4), b_p__p_);
      const b_p__p__p__p_ = (((b_p__p__p_).writeUInt16BE)(checksum, 6), b_p__p__p_);
      const b_p__p__p__p__p_ = (((contents).copy)(b_p__p__p__p_, 8, 0, len_p_), b_p__p__p__p_);
      return b_p__p__p__p__p_;
    })();
    return new_p;
  })()) : (null);
})();
const main = (() => {
  const test_packet = (() => {
    const len_p_ = 3;
    const total_len = (len_p_) + (8);
    const b = (Buffer.allocUnsafe)(total_len);
    const b_p_ = (((b).writeUInt16BE)(2, 0), b);
    const b_p__p_ = (((b_p_).writeUInt16BE)(3, 2), b_p_);
    const b_p__p__p_ = (((b_p__p_).writeUInt16BE)(len_p_, 4), b_p__p_);
    const b_p__p__p__p_ = (((b_p__p__p_).writeUInt16BE)(5, 6), b_p__p__p_);
    const b_p__p__p__p__p_ = ((((() => {
      const xs_p_ = (() => {
        const xs_p_ = (() => {
          const xs_p_ = (Buffer.allocUnsafe)(0);
          const old_len = (Buffer.byteLength)(xs_p_);
          const new_len = (old_len) + (1);
          const b = (Buffer.allocUnsafe)(new_len);
          const b_p_ = (((b).writeUInt8)(3, 0), b);
          return (((xs_p_).copy)(b_p_, 1, 0, old_len), b_p_);
        })();
        const old_len = (Buffer.byteLength)(xs_p_);
        const new_len = (old_len) + (1);
        const b = (Buffer.allocUnsafe)(new_len);
        const b_p_ = (((b).writeUInt8)(2, 0), b);
        return (((xs_p_).copy)(b_p_, 1, 0, old_len), b_p_);
      })();
      const old_len = (Buffer.byteLength)(xs_p_);
      const new_len = (old_len) + (1);
      const b = (Buffer.allocUnsafe)(new_len);
      const b_p_ = (((b).writeUInt8)(1, 0), b);
      return (((xs_p_).copy)(b_p_, 1, 0, old_len), b_p_);
    })()).copy)(b_p__p__p__p_, 8, 0, len_p_), b_p__p__p__p_);
    return b_p__p__p__p__p_;
  })();
  const result = (handle_packet)(test_packet);
  return (() => (((_) => ((debug_print)(null))(result))((((debug_print)(null))(test_packet))()))());
})();
(main)()