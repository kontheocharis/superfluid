const { Buffer } = require('node:buffer');
const prompt = require('prompt-sync')();
const id = (A) => (a) => a;
const if_then_else = (A) => (b) => (t) => (f) => (b) ? ((t)(["tt"])) : ((f)(["tt"]));
const debug_print = (A) => (a) => (() => ((console).log)(a));
const sub = (m) => (n) => ((n) === (0)) ? (m) : (((m) === (0)) ? (0) : (((sub)((m) - (1)))((n) - (1))));
const find = (A) => (p) => (xs) => (((xs).length) === (0)) ? (null) : (((p)((xs)[0])) ? ((xs)[0]) : ((((find)(A))(p))((xs).slice(1, (xs).length))));
const Char = null;
const STRING = null;
const fib = (n) => ((r) => ((n) === (0)) ? (0) : ((r)((n) - (1))))((n_p_) => ((n_p_) === (0)) ? ((1) + (0)) : (((fib)(n_p_)) + ((fib)((n_p_) - (1)))));
const identity = ["lam", ["var", 0]];
const two = (1) + ((1) + (0));
const ten = (1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + (0))))))))));
const twenty = ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + (0))))))))))) * (two);
const test_list = ((xs) => [(1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + (0)))))))))), ...(xs)])([twenty, ...([(1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + (0)))))))))), ...([twenty, ...([])])])]);
const main = ((debug_print)(null))(((xs) => (xs).map((x) => (x) ** (two)))(test_list));
(main)()