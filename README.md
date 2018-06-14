# Code from `The Reasoned Schemer, Second Edition`

Code from The Reasoned Schemer, Second Edition, by Daniel P. Friedman, William E. Byrd, Oleg Kiselyov and Jason Hemann, 2018 MIT Press


`trs2-impl.scm` includes the implementation of the language used in the book, from Chapter 10 &amp; Appendix A

`trs2-arith.scm` includes the arithmetic relations from Chapters 7 &amp; 8 (please load `trs2-impl.scm` before loading `trs2-arith.scm`)


## Example of loading and testing the code in Scheme, assuming you start Scheme in the same directory as the code

```
> (load "trs2-impl.scm")
> (run* q (== 'pasta q))
(pasta)
> (load "trs2-arith.scm")
> (run* q (*o (build-num 3) (build-num 4) q))
((0 0 1 1))
>
```
