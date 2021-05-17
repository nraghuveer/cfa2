let halt = x => console.log(x)

function fact (n, k1) {
	let u10 = n <= 1.0
	if (u10) {
		k1(1.0) /*7*/ /*KApp*/
	}
	else {
		let k13 = x11 => {
			let u15 = n * x11
			k1(u15) /*10*/ /*KApp*/ /*ULet*/
		} /* KLam */
		let u16 = n - 1.0
		fact(u16, k13) /*11*/ /*UApp*/ /*ULet*/ /*KLet*/
	} /*ULet*/
}

let k19 = x17 => {
	let x = x17
	fact(x, halt) /*17*/ /*TcUApp*/ /*ULet*/
} /* KLam */
fact(3.0, k19) /*18*/ /*UApp*/ /*KLet*/