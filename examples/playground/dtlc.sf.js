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
const main = (() => {
  const y = [3, ...([])];
  return ((debug_print)(null))(y);
})();
(main)()