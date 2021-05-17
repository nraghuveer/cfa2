let halt = x => console.log(x)

function f (x, k1) {
	k1(x) /*1*/ /*KApp*/
}
function g (y, k2) {
	k2(y) /*2*/ /*KApp*/
}

let k7 = x6 => {
	x6(g, halt) /*8*/ /*TcUApp*/
} /* KLam */
f(f, k7) /*9*/ /*UApp*/ /*KLet*/