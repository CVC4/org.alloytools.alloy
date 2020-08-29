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
(declare-fun accountAtom () Atom)
(declare-fun |this/BankAccount/deposit | () (Set (Tuple Atom UInt UInt)))
(declare-fun |this/BankAccount/withdrawal | () (Set (Tuple Atom UInt UInt)))
(declare-fun |this/BankAccount/balance | () (Set (Tuple Atom UInt UInt)))
(declare-fun zero () UInt)
(declare-fun one () UInt)
(define-fun |this/depositValue | ((|t| (Tuple UInt))) (Tuple UInt)
 (choose
 (join
   (join |this/BankAccount |; this/BankAccount
     |this/BankAccount/deposit |; (this/BankAccount <: deposit)
    ) (singleton |t|); t
  )))
(define-fun |this/withdrawalValue | ((|t| (Tuple UInt))) (Tuple UInt)
(choose
 (join
   (join |this/BankAccount |; this/BankAccount
     |this/BankAccount/withdrawal |; (this/BankAccount <: withdrawal)
    ) (singleton |t|); t
  )))
(define-fun |this/balanceValue | ((|t| (Tuple UInt))) (Tuple UInt)
(choose
 (join
   (join |this/BankAccount |; this/BankAccount
     |this/BankAccount/balance |; (this/BankAccount <: balance)
    ) (singleton |t|); t
  )))
(define-fun |this/deposit | ((|t| (Tuple UInt))(|t'|  (Tuple UInt))(amount (Tuple UInt))) Bool
 (and
    (> (intValue ((_ tupSel 0) amount)) (intValue zero))
    (= (|this/depositValue | |t'|) amount)
    (= (|this/withdrawalValue | |t'|)  (mkTuple zero))
   (exists ((z UInt))
     (and
       (= (mkTuple z) (|this/balanceValue | |t'|))
       (exists ((x UInt)(y UInt))
         (and
           (= (+ (intValue x) (intValue y)) (intValue z))
           (= (mkTuple x) (|this/balanceValue | |t|))
           (= (mkTuple y) amount )))))))

(define-fun |this/withdraw | ((|t| (Tuple UInt))(|t'|  (Tuple UInt))(amount (Tuple UInt))) Bool
 (and
   (> (intValue ((_ tupSel 0) amount)) (intValue zero))
   (exists ((x UInt)(y UInt))
     (and
       (= (mkTuple x) (|this/balanceValue | |t|))
       (= (mkTuple y) amount)
       (>= (intValue x) (intValue y))))
   (= (|this/depositValue | |t'|) (mkTuple zero))
   (= (|this/withdrawalValue | |t'|) amount)
   (exists ((z UInt))
     (and
       (= (mkTuple z) (|this/balanceValue | |t'|))
       (exists ((x UInt)(y UInt))
         (and
           (= (- (intValue x) (intValue y)) (intValue z))
           (= (mkTuple x) (|this/balanceValue | |t|))
           (= (mkTuple y) amount)))))))

(define-fun |this/init | ((|t| (Tuple UInt))) Bool
 (and
   (=
     (join
       (join |this/BankAccount |; this/BankAccount
         |this/BankAccount/deposit |; (this/BankAccount <: deposit)
        ) (singleton |t|); t
      )
     (singleton
       (mkTuple zero)))
   (=
     (join
       (join |this/BankAccount |; this/BankAccount
         |this/BankAccount/withdrawal |; (this/BankAccount <: withdrawal)
        ) (singleton |t|); t
      )
     (singleton
       (mkTuple zero)))
   (=
     (join
       (join |this/BankAccount |; this/BankAccount
         |this/BankAccount/balance |; (this/BankAccount <: balance)
        ) (singleton |t|); t
      )
     (singleton
       (mkTuple zero)))))

(define-fun |this/someTransaction | ((|t| (Tuple UInt))(|t'| (Tuple UInt))) Bool

 (exists ((x UInt))
   (let ((amount    (mkTuple x)))
     (and
        (member amount univInt)
        (or
            (|this/deposit | |t|  |t'| amount))
            (|this/withdraw | |t| |t'| amount)))))

(define-fun |this/system | () Bool
 (and
    (|this/init | (mkTuple zero))
    (forall ((u UInt))
     (let ((|t'| (mkTuple u)))
       (=>
         (and
            (member |t'| |this/Time |)
            (not (= |t'| (mkTuple zero))))
         (exists ((t UInt))
            (and
                (= (- (intValue u) (intValue one)) (intValue t))
                (|this/someTransaction | (mkTuple t) |t'|))))))))


; one this/BankAccount
(assert
 (= |this/BankAccount |; this/BankAccount

   (singleton
     (mkTuple accountAtom))))

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
 (= (intValue zero) 0))

; nonNegative
(assert
 (forall ((t UInt))
     (=>
       (member (mkTuple t) |this/Time |)
       (>= (intValue t) (intValue zero)))))

; constant integer
(assert (= (intValue one) 1))

; noGaps {all t: Time - 0 | minus[t,1] in Time }
(assert
 (forall ((u.55 UInt))
   (let ((|t| (mkTuple u.55)))
     (=>
       (and
        (member |t| |this/Time |)
        (not (= u.55 zero)))
       (exists ((z UInt))
         (and
            (= (- (intValue u.55) (intValue one)) (intValue z))
            (member (mkTuple z) |this/Time |)))))))

; universe
(assert (= |integer/univInt | univInt))

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
 (forall ((accountAtom Atom)(a.2 Atom))
   (=
     (member
       (mkTuple accountAtom a.2) idenAtom)
     (= accountAtom a.2))))

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
 (= (intValue zero) 0))

; assert sanity
; {
;     all  t': Time - 0, a : univInt |
;     let t = minus[t',1] | -- t' = t + 1
;     {
;         withdraw[t, t', a]
;         implies
;         balanceValue[t'] < balanceValue[t]
;     }
; }

(assert
 (not
   (forall ((|t'| UInt)(|a| UInt))
       (=>
         (and
           (member (mkTuple |t'|) |this/Time |)
           (not (= |t'| zero))
           (member (mkTuple |a|) |integer/univInt |))
         (exists ((|t| UInt)) ; t = minus[t',1]
           (and
              (= (- (intValue |t'|) (intValue one)) (intValue |t|))
              (=>
                (|this/withdraw | (mkTuple |t|) (mkTuple |t'|) (mkTuple |a|))
                 (<
                    (intValue ((_ tupSel 0) (|this/balanceValue | (mkTuple |t'|))))
                    (intValue ((_ tupSel 0) (|this/balanceValue | (mkTuple |t| ))))))))))))
(check-sat)

