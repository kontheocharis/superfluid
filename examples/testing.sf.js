const prompt = require('prompt-sync')();
const id = (A) => (a) => a;
const debug_print = (A) => (a) => (() => ((console).log)(a));
const find = (A) => (p) => (xs) => (((xs).length) === (0)) ? (null) : (((p)((xs)[0])) ? ((xs)[0]) : ((((find)(A))(p))((xs).slice(1, (xs).length))));
const Char = null;
const STRING = null;
const fib = (n) => ((n) === (0)) ? (0) : ((((n) - (1)) === (0)) ? ((1) + (0)) : (((fib)((n) - (1))) + ((fib)(((n) - (1)) - (1)))));
const two = (1) + ((1) + (0));
const ten = (1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + (0))))))))));
const twenty = (ten) * (two);
const test_list = [ten, ...([twenty, ...([ten, ...([twenty, ...([])])])])];
const main = ((debug_print)(null))((test_list).map((x) => (x) ** (two)));
(main)()