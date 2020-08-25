(set-logic ALL)
(set-option :cegqi-all false)
(set-option :block-models literals)
(set-option :finite-model-find true)
(set-option :produce-models true)
(set-option :incremental true)
(set-option :sets-ext true)
(declare-sort Atom 0)
(declare-sort UInt 0)
(declare-fun intValue (UInt) Int)
(declare-fun atomNone () (Set (Tuple Atom)))
(declare-fun univAtom () (Set (Tuple Atom)))
(declare-fun idenAtom () (Set (Tuple Atom Atom)))
(declare-fun idenInt () (Set (Tuple UInt UInt)))
(declare-fun univInt () (Set (Tuple UInt)))
(declare-fun |this/Time | () (Set (Tuple UInt)))
(declare-fun |this/BankAccount | () (Set (Tuple Atom)))
(declare-fun |integer/univInt | () (Set (Tuple UInt)))
(declare-fun a.1 () Atom)
(declare-fun |this/BankAccount/deposit | () (Set (Tuple Atom UInt UInt)))
(declare-fun |this/BankAccount/withdrawal | () (Set (Tuple Atom UInt UInt)))
(declare-fun |this/BankAccount/balance | () (Set (Tuple Atom UInt UInt)))
(declare-fun u.9_0 () UInt)
(declare-fun u.11_1 () UInt)
(define-fun |this/depositValue | ((tTuple (Set (Tuple UInt)))) (Set (Tuple UInt))

 (join
   (join |this/BankAccount |; this/BankAccount
     |this/BankAccount/deposit |; (this/BankAccount <: deposit)
    ) tTuple; t
  ))
(define-fun |this/withdrawalValue | ((tTuple (Set (Tuple UInt)))) (Set (Tuple UInt))

 (join
   (join |this/BankAccount |; this/BankAccount
     |this/BankAccount/withdrawal |; (this/BankAccount <: withdrawal)
    ) tTuple; t
  ))
(define-fun |this/balanceValue | ((tTuple (Set (Tuple UInt)))) (Set (Tuple UInt))

 (join
   (join |this/BankAccount |; this/BankAccount
     |this/BankAccount/balance |; (this/BankAccount <: balance)
    ) tTuple; t
  ))
(define-fun |this/deposit | ((tTuple (Set (Tuple UInt)))(uTuple (Set (Tuple UInt)))(|amount | (Set (Tuple UInt)))) Bool

 (and
   (exists ((x UInt)(y UInt))
     (and
       (=
         (singleton
           (mkTuple x)) |amount |; int[amount]
        )
       (=
         (singleton
           (mkTuple y))
         (singleton
           (mkTuple u.9_0)))
       (> (intValue x) (intValue y))))
   (= (|this/depositValue | uTuple; t'
    ) |amount |; int[amount]
    )
   (= (|this/withdrawalValue | uTuple; t'
    )
     (singleton
       (mkTuple u.9_0)))
   (exists ((z UInt))
     (and
       (=
         (singleton
           (mkTuple z)) (|this/balanceValue | uTuple; t'
        ))
       (exists ((x UInt)(y UInt))
         (and
           (=
             (+ (intValue x) (intValue y)) (intValue z))
           (=
             (singleton
               (mkTuple x)) (|this/balanceValue | tTuple; t
            ))
           (=
             (singleton
               (mkTuple y)) |amount |; int[amount]
            )))))))
(define-fun |this/withdraw | ((tTuple (Set (Tuple UInt)))(uTuple (Set (Tuple UInt)))(|amount | (Set (Tuple UInt)))) Bool

 (and
   (exists ((x UInt)(y UInt))
     (and
       (=
         (singleton
           (mkTuple x)) |amount |; int[amount]
        )
       (=
         (singleton
           (mkTuple y))
         (singleton
           (mkTuple u.9_0)))
       (> (intValue x) (intValue y))))
   (exists ((x UInt)(y UInt))
     (and
       (=
         (singleton
           (mkTuple x)) (|this/balanceValue | tTuple; t
        ))
       (=
         (singleton
           (mkTuple y)) |amount |; int[amount]
        )
       (>= (intValue x) (intValue y))))
   (= (|this/depositValue | uTuple; t'
    )
     (singleton
       (mkTuple u.9_0)))
   (= (|this/withdrawalValue | uTuple; t'
    ) |amount |; int[amount]
    )
   (exists ((z UInt))
     (and
       (=
         (singleton
           (mkTuple z)) (|this/balanceValue | uTuple; t'
        ))
       (exists ((x UInt)(y UInt))
         (and
           (=
             (- (intValue x) (intValue y)) (intValue z))
           (=
             (singleton
               (mkTuple x)) (|this/balanceValue | tTuple; t
            ))
           (=
             (singleton
               (mkTuple y)) |amount |; int[amount]
            )))))))
(define-fun |this/init | ((tTuple (Set (Tuple UInt)))) Bool

 (and
   (=
     (join
       (join |this/BankAccount |; this/BankAccount
         |this/BankAccount/deposit |; (this/BankAccount <: deposit)
        ) tTuple; t
      )
     (singleton
       (mkTuple u.9_0)))
   (=
     (join
       (join |this/BankAccount |; this/BankAccount
         |this/BankAccount/withdrawal |; (this/BankAccount <: withdrawal)
        ) tTuple; t
      )
     (singleton
       (mkTuple u.9_0)))
   (=
     (join
       (join |this/BankAccount |; this/BankAccount
         |this/BankAccount/balance |; (this/BankAccount <: balance)
        ) tTuple; t
      )
     (singleton
       (mkTuple u.9_0)))))
(define-fun |this/someTransaction | ((tTuple (Set (Tuple UInt)))(uTuple (Set (Tuple UInt)))) Bool

 (exists ((u.40 UInt))
   (let (
    (|amount |
     (mkTuple u.40)))
     (and
       (member |amount | univInt; Int
        )
       (or (|this/deposit | tTuple; t
         uTuple; t'

         (singleton |amount |)) (|this/withdraw | tTuple; t
         uTuple; t'

         (singleton |amount |)))))))
(define-fun |this/system | () Bool

 (and (|this/init |
   (singleton
     (mkTuple u.9_0)))
   (forall ((u.41 UInt))
     (let (
      (uTuple
       (mkTuple u.41)))
       (=>
         (member uTuple
           (setminus |this/Time |; this/Time

             (singleton
               (mkTuple u.9_0))))
         (exists ((s.19 (Set (Tuple UInt))))
           (and
             (forall ((z UInt))
               (=>
                 (member
                   (mkTuple z) s.19; integer/minus[t', Int[1]]
                  )
                 (exists ((x UInt)(y UInt))
                   (and
                     (=
                       (- (intValue x) (intValue y)) (intValue z))
                     (member
                       (mkTuple x)
                       (singleton uTuple))
                     (member
                       (mkTuple y)
                       (singleton
                         (mkTuple u.11_1)))))))
             (forall ((x UInt)(y UInt))
               (=>
                 (and
                   (member
                     (mkTuple x)
                     (singleton uTuple))
                   (member
                     (mkTuple y)
                     (singleton
                       (mkTuple u.11_1))))
                 (exists ((z UInt))
                   (and
                     (=
                       (- (intValue x) (intValue y)) (intValue z))
                     (member
                       (mkTuple z) s.19; integer/minus[t', Int[1]]
                      )))))
             (let (
              (tTuple s.19; integer/minus[t', Int[1]]
              )) (|this/someTransaction | tTuple; t

               (singleton uTuple))))))))))
(declare-fun u.20_10 () UInt)
(declare-fun u.21_2 () UInt)
(declare-fun u.22_40 () UInt)
(declare-fun u.23_3 () UInt)
(declare-fun u.24_30 () UInt)
(define-fun |this/run$2 | () Bool

 (and (|this/init |
   (singleton
     (mkTuple u.9_0))) (|this/deposit |
   (singleton
     (mkTuple u.9_0))
   (singleton
     (mkTuple u.11_1))
   (singleton
     (mkTuple u.20_10))) (|this/deposit |
   (singleton
     (mkTuple u.11_1))
   (singleton
     (mkTuple u.21_2))
   (singleton
     (mkTuple u.22_40))) (|this/withdraw |
   (singleton
     (mkTuple u.21_2))
   (singleton
     (mkTuple u.23_3))
   (singleton
     (mkTuple u.24_30)))))
(declare-fun u.25_50 () UInt)
(define-fun |this/run$3 | () Bool

 (and |this/system |
   (= (|this/balanceValue |
     (singleton
       (mkTuple u.21_2)))
     (singleton
       (mkTuple u.25_50)))))
(define-fun |this/nonNegative | ((tTuple (Set (Tuple UInt)))) Bool

 (and
   (exists ((x UInt)(y UInt))
     (and
       (=
         (singleton
           (mkTuple x)) (|this/depositValue | tTuple; t
        ))
       (=
         (singleton
           (mkTuple y))
         (singleton
           (mkTuple u.9_0)))
       (>= (intValue x) (intValue y))))
   (exists ((x UInt)(y UInt))
     (and
       (=
         (singleton
           (mkTuple x)) (|this/withdrawalValue | tTuple; t
        ))
       (=
         (singleton
           (mkTuple y))
         (singleton
           (mkTuple u.9_0)))
       (>= (intValue x) (intValue y))))
   (exists ((x UInt)(y UInt))
     (and
       (=
         (singleton
           (mkTuple x)) (|this/balanceValue | tTuple; t
        ))
       (=
         (singleton
           (mkTuple y))
         (singleton
           (mkTuple u.9_0)))
       (>= (intValue x) (intValue y))))))

; one this/BankAccount
(assert
 (= |this/BankAccount |; this/BankAccount

   (singleton
     (mkTuple a.1))))

; atomUniv is the union of top level signatures
(assert
 (= |this/BankAccount |; this/BankAccount
   univAtom))

; field (this/BankAccount <: deposit) multiplicity
(assert
 (forall ((x Atom))
   (=>
     (member
       (mkTuple x) |this/BankAccount |; this/BankAccount
      )
     (forall ((y UInt))
       (=>
         (member
           (mkTuple y) |this/Time |; this/Time
          )
         (exists ((z UInt))
           (and
             (member
               (mkTuple z) univInt; Int
              )
             (member
               (mkTuple x z y) |this/BankAccount/deposit |; (this/BankAccount <: deposit)
              )
             (forall ((w UInt))
               (=>
                 (not
                   (= w z))
                 (not
                   (member
                     (mkTuple x w y) |this/BankAccount/deposit |; (this/BankAccount <: deposit)
                    )))))))))))

; field (this/BankAccount <: deposit) subset
(assert
 (subset |this/BankAccount/deposit |; (this/BankAccount <: deposit)

   (product |this/BankAccount |; this/BankAccount

     (product univInt; Int
       |this/Time |; this/Time
      ))))

; field (this/BankAccount <: withdrawal) multiplicity
(assert
 (forall ((x Atom))
   (=>
     (member
       (mkTuple x) |this/BankAccount |; this/BankAccount
      )
     (forall ((y UInt))
       (=>
         (member
           (mkTuple y) |this/Time |; this/Time
          )
         (exists ((z UInt))
           (and
             (member
               (mkTuple z) univInt; Int
              )
             (member
               (mkTuple x z y) |this/BankAccount/withdrawal |; (this/BankAccount <: withdrawal)
              )
             (forall ((w UInt))
               (=>
                 (not
                   (= w z))
                 (not
                   (member
                     (mkTuple x w y) |this/BankAccount/withdrawal |; (this/BankAccount <: withdrawal)
                    )))))))))))

; field (this/BankAccount <: withdrawal) subset
(assert
 (subset |this/BankAccount/withdrawal |; (this/BankAccount <: withdrawal)

   (product |this/BankAccount |; this/BankAccount

     (product univInt; Int
       |this/Time |; this/Time
      ))))

; field (this/BankAccount <: balance) multiplicity
(assert
 (forall ((x Atom))
   (=>
     (member
       (mkTuple x) |this/BankAccount |; this/BankAccount
      )
     (forall ((y UInt))
       (=>
         (member
           (mkTuple y) |this/Time |; this/Time
          )
         (exists ((z UInt))
           (and
             (member
               (mkTuple z) univInt; Int
              )
             (member
               (mkTuple x z y) |this/BankAccount/balance |; (this/BankAccount <: balance)
              )
             (forall ((w UInt))
               (=>
                 (not
                   (= w z))
                 (not
                   (member
                     (mkTuple x w y) |this/BankAccount/balance |; (this/BankAccount <: balance)
                    )))))))))))

; field (this/BankAccount <: balance) subset
(assert
 (subset |this/BankAccount/balance |; (this/BankAccount <: balance)

   (product |this/BankAccount |; this/BankAccount

     (product univInt; Int
       |this/Time |; this/Time
      ))))

; Signature fact 'AND[some this/BankAccount . (this/BankAccount <: deposit), some this/BankAccount . (this/BankAccount <: withdrawal), some this/BankAccount . (this/BankAccount <: balance)]' for sig this/BankAccount
(assert
 (forall ((|this | Atom))
   (=>
     (member
       (mkTuple |this |) |this/BankAccount |; this/BankAccount
      )
     (and
       (not
         (=
           (join |this/BankAccount |; this/BankAccount
             |this/BankAccount/deposit |; (this/BankAccount <: deposit)
            )
           (as emptyset (Set (Tuple UInt UInt)))))
       (not
         (=
           (join |this/BankAccount |; this/BankAccount
             |this/BankAccount/withdrawal |; (this/BankAccount <: withdrawal)
            )
           (as emptyset (Set (Tuple UInt UInt)))))
       (not
         (=
           (join |this/BankAccount |; this/BankAccount
             |this/BankAccount/balance |; (this/BankAccount <: balance)
            )
           (as emptyset (Set (Tuple UInt UInt)))))))))

; constant integer
(assert
 (= (intValue u.9_0) 0))

; positive
(assert
 (forall ((u.54 UInt))
   (let (
    (tTuple
     (mkTuple u.54)))
     (=>
       (member tTuple |this/Time |; this/Time
        )
       (exists ((x UInt)(y UInt))
         (and
           (=
             (singleton
               (mkTuple x))
             (singleton tTuple))
           (=
             (singleton
               (mkTuple y))
             (singleton
               (mkTuple u.9_0)))
           (>= (intValue x) (intValue y))))))))

; constant integer
(assert
 (= (intValue u.11_1) 1))

; noGaps
(assert
 (forall ((u.55 UInt))
   (let (
    (tTuple
     (mkTuple u.55)))
     (=>
       (member tTuple
         (setminus |this/Time |; this/Time

           (singleton
             (mkTuple u.9_0))))
       (exists ((s.12 (Set (Tuple UInt))))
         (and
           (forall ((z UInt))
             (=>
               (member
                 (mkTuple z) s.12; integer/minus[t, Int[1]]
                )
               (exists ((x UInt)(y UInt))
                 (and
                   (=
                     (- (intValue x) (intValue y)) (intValue z))
                   (member
                     (mkTuple x)
                     (singleton tTuple))
                   (member
                     (mkTuple y)
                     (singleton
                       (mkTuple u.11_1)))))))
           (forall ((x UInt)(y UInt))
             (=>
               (and
                 (member
                   (mkTuple x)
                   (singleton tTuple))
                 (member
                   (mkTuple y)
                   (singleton
                     (mkTuple u.11_1))))
               (exists ((z UInt))
                 (and
                   (=
                     (- (intValue x) (intValue y)) (intValue z))
                   (member
                     (mkTuple z) s.12; integer/minus[t, Int[1]]
                    )))))
           (subset s.12; integer/minus[t, Int[1]]
             |this/Time |; this/Time
            )))))))

; universe
(assert
 (= |integer/univInt |; integer/univInt
   univInt; Int
  ))

; identity
(assert
 (forall ((u.56 UInt)(u.57 UInt))
   (let (
    (|x |
     (mkTuple u.56))
    (|y |
     (mkTuple u.57)))
     (=>
       (and
         (member |x | |integer/univInt |; integer/univInt
          )
         (member |y | |integer/univInt |; integer/univInt
          ))
       (=
         (=
           (singleton |x |)
           (singleton |y |))
         (subset
           (product
             (singleton |x |)
             (singleton |y |)) idenInt; (integer/univInt <: idenInt)
          ))))))

; Empty unary relation definition for Atom
(assert
 (= atomNone
   (as emptyset (Set (Tuple Atom)))))

; Universe definition for Atom
(assert
 (= univAtom
   (as univset (Set (Tuple Atom)))))

; Universe definition for UninterpretedInt
(assert
 (= univInt; Int

   (as univset (Set (Tuple UInt)))))

; Identity relation definition for idenAtom
(assert
 (forall ((a.1 Atom)(a.2 Atom))
   (=
     (member
       (mkTuple a.1 a.2) idenAtom)
     (= a.1 a.2))))

; Identity relation definition for idenInt
(assert
 (forall ((u.3 UInt)(u.4 UInt))
   (=
     (member
       (mkTuple u.3 u.4) idenInt; (integer/univInt <: idenInt)
      )
     (= u.3 u.4))))

; intValue is injective
(assert
 (forall ((x UInt)(y UInt))
   (=>
     (not
       (= x y))
     (not
       (= (intValue x) (intValue y))))))

; constant integer
(assert
 (= (intValue u.20_10) 10))

; constant integer
(assert
 (= (intValue u.21_2) 2))

; constant integer
(assert
 (= (intValue u.22_40) 40))

; constant integer
(assert
 (= (intValue u.23_3) 3))

; constant integer
(assert
 (= (intValue u.24_30) 30))

; constant integer
(assert
 (= (intValue u.25_50) 50))

(declare-fun zero () UInt)
(declare-fun u.29_1 () UInt)

; constant integer
(assert
 (= (intValue zero) 0))

; constant integer
(assert
 (= (intValue u.29_1) 1))



; ! (all t',a | (let t= integer/minus[t', Int[1]] | this/withdraw[t, t', a] => int[this/balanceValue[t']] < int[this/balanceValue[t]]))
(assert
 (not
   (forall ((u UInt)(a UInt))
     (let (
      (uTuple
       (mkTuple u))
      (aTuple
       (mkTuple a)))
       (=>
         (and
           (member uTuple |this/Time |)
           (not (= u zero)))

         (exists ((t UInt))
            (and
                (= (- (intValue u) (intValue u.29_1)) (intValue t))
             (let (
              (tTuple (singleton (mkTuple t)); integer/minus[t', Int[1]]
              ))
               (=> (|this/withdraw | tTuple; t

                 (singleton uTuple)
                 (singleton aTuple))
                 (exists ((x UInt)(y UInt))
                   (and
                     (=
                       (singleton
                         (mkTuple x)) (|this/balanceValue |
                       (singleton uTuple)))
                     (=
                       (singleton
                         (mkTuple y)) (|this/balanceValue | tTuple; t
                      ))
                     (< (intValue x) (intValue y)))))))))))))


(check-sat)
(get-model)
