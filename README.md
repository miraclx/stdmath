# stdmath

A collection of useful mathematical methods implemented in Rust

![CI](https://github.com/miraclx/stdmath/workflows/CI/badge.svg) ![Apache 2.0](https://img.shields.io/github/license/miraclx/stdmath)

> STDMATH HAS MORPHED. It's no longer just a "collection of useful mathematical methods implemented in Rust" but now a math expression optimization library. Documentation hasn't been updated to reflect this but if you can, please see the tests [here](https://github.com/miraclx/stdmath/blob/master/src/core.rs). There's still a lot of work to do, so this is heavily WIP.

## Methods

### Sigma ([docs][sigma])

<img src="https://render.githubusercontent.com/render/math?math=%5Cdisplaystyle+%5Csum_%7Bstart%7D%5E%7Bstop%7Dfunc" alt="\sum_{start}^{stop}func">

### Product ([docs][product])

<img src="https://render.githubusercontent.com/render/math?math=%5Cdisplaystyle+%5Cprod_%7Bstart%7D%5E%7Bstop%7Dfunc" alt="\prod_{start}^{stop}func">

### Factorial ([docs][factorial])

<img src="https://render.githubusercontent.com/render/math?math=%5Cdisplaystyle+val%21+%3D+%5Cprod_%7Bx%3D1%7D%5E%7Bval%7Dx" alt="val! = \prod_{x=1}^{val}x">

### Factorial Count ([docs][factorial_count])

<img src="https://render.githubusercontent.com/render/math?math=%5Cdisplaystyle+%5Csum_%7Bn%3D1%7D%5E%7Bval%7D%5Cleft%5Clfloor%5Clog_%7B10%7Dn%5Cright%5Crfloor%2B1" alt="\sum_{n=1}^{val}\left\lfloor\log_{10}n\right\rfloor+1">

### Combination ([docs][combination])

method             | representation
------------------ | :------------:
without repetition | <img src="https://render.githubusercontent.com/render/math?math=%5Cdisplaystyle+%7B%7D%5EnC_r+%3D+%5Cfrac%7Bn%21%7D%7B%28r%21%5Ctimes%28n-r%29%21%29%21%7D" alt="{}^nC_r = \frac{n!}{(r!\times(n-r)!)!}">
with repetition    | <img src="https://render.githubusercontent.com/render/math?math=%5Cdisplaystyle+%7B%7D%5EnC_r+%3D+%5Cfrac%7B%28n%2Br-1%29%21%7D%7Br%21%5Ctimes%28n-1%29%21%7D" alt="{}^nC_r = \frac{(n+r-1)!}{r!\times(n-1)!}">

### Permutation ([docs][permutation])

method             | representation
------------------ | :------------:
without repetition | <img src="https://render.githubusercontent.com/render/math?math=%5Cdisplaystyle+%7B%7D%5EnP_r+%3D+%5Cfrac%7Bn%21%7D%7B%28n-r%29%21%7D" alt="{}^nP_r = \frac{n!}{(n-r)!}">
with repetition    | <img src="https://render.githubusercontent.com/render/math?math=%5Cdisplaystyle+%7B%7D%5EnP_r+%3D+n%5Er" alt="{}^nP_r = n^r">

### Binomial ([docs][binomial])

<img src= "https://render.githubusercontent.com/render/math?math=%5Cdisplaystyle+%28a%2Bb%29%5En+%3D+%5Csum_%7Br%3D0%7D%5E%7Bn%7D%7B%7D%5EnC_r+%5Ctimes%7Ba%5E%7Bn-r%7D%7D%5Ctimes%7Bb%5Er%7D" alt="(a+b)^n = \sum_{r=0}^{n}{}^nC_r \times{a^{n-r}}\times{b^r}">

### Pascals Triangle ([docs][pascals])

Draws the pascals triangle

#### Example

``` rust
vec![
    vec![1],
    vec![1, 1],
    vec![1, 2, 1],
    vec![1, 3, 3, 1],
    vec![1, 4, 6, 4, 1],
    vec![1, 5, 10, 10, 5, 1],
    vec![1, 6, 15, 20, 15, 6, 1],
]
```

### ramanujansPI ([docs][ramanujansPI])

<img src="https://render.githubusercontent.com/render/math?math=%5Cdisplaystyle+%5Cfrac%7B1%7D%7B%5Cpi%7D%3D%5Cfrac%7B%5Csqrt%7B8%7D%7D%7B9801%7D%5Csum_%7Bn%3D0%7D%5E%7B%5Cinfty%7D%5Cfrac%7B%284n%29%21%7D%7B%28n%21%29%5E4%7D%5Ctimes%5Cfrac%7B26390n+%2B+1103%7D%7B396%5E%7B4n%7D%7D" alt="\frac{1}{\pi}=\frac{\sqrt{8}}{9801}\sum_{n=0}^{\infty}\frac{(4n)!}{(n!)^4}\times\frac{26390n + 1103}{396^{4n}}">

## License

`stdmath` is licensed under the Apache License, Version 2.0.
See ([LICENSE](LICENSE) or <http://www.apache.org/licenses/LICENSE-2.0>) for more details.

[binomial]: https://miraclx.github.io/stdmath/math/fn.binomial.html
[combination]: https://miraclx.github.io/stdmath/math/fn.combination.html
[factorial]: https://miraclx.github.io/stdmath/math/fn.factorial.html
[factorial_count]: https://miraclx.github.io/stdmath/math/fn.factorial_count.html
[pascals]: https://miraclx.github.io/stdmath/math/fn.pascals.html
[permutation]: https://miraclx.github.io/stdmath/math/fn.permutation.html
[product]: https://miraclx.github.io/stdmath/math/fn.product.html
[ramanujansPI]: https://miraclx.github.io/stdmath/math/fn.ramanujansPI.html
[sigma]: https://miraclx.github.io/stdmath/math/fn.sigma.html
