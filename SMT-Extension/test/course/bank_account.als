sig Time in Int {}
fact nonNegative {all t: Time | t >= 0}
fact noGaps {all t: Time | t != 0 implies minus[t,1] in Time }
one sig BankAccount
{
    deposit: Int one -> Time,
    withdrawal: Int one-> Time,
    balance: Int one-> Time
}
{some deposit and some withdrawal and some balance}
fun depositValue[t: one Time]: one Int {BankAccount.deposit.t}
fun withdrawalValue[t: one Time]: one Int {BankAccount.withdrawal.t}
fun balanceValue[t: one Time]: one Int {BankAccount.balance.t}
pred deposit[t, t' : one Time, amount: one Int]
{
    amount > 0
    depositValue[t'] = amount
    withdrawalValue[t'] = 0
    balanceValue[t'] = plus[balanceValue[t], amount]
}
pred withdraw[t, t' : one Time, amount: one Int]
{
    amount > 0
    balanceValue[t] >= amount -- there is enough balance at t
    depositValue[t'] = 0
    withdrawalValue[t'] = amount
    balanceValue[t'] = minus[balanceValue[t], amount]
}

assert sanity
{
    all  t': Time, a : univInt | t' != 0 implies
    let t = minus[t',1] |
    {
        withdraw[t, t', a]  
        implies
        balanceValue[t'] < balanceValue[t]
    }
}
check sanity

pred init [t: one Time]
{
  BankAccount.deposit.t = 0
  BankAccount.withdrawal.t = 0
  BankAccount.balance.t = 0
}

pred someTransaction[t, t': one Time]
{
  some amount : Int | deposit[t, t', amount] iff not withdraw[t, t', amount]
}


pred system
{
  init[0]
  all t': Time | t' != 0 implies  let t = minus[t',1]  | someTransaction[t, t']
}

fact {system}

run scenario1
{
  init[0]
  deposit[0, 1, 10]
  deposit[1, 2, 40]
  withdraw[2, 3, 30]
} for 7 Int
run scenario2
{
 system
 balanceValue[2] = 50
} for 7 Int
pred nonNegative [t: Time]
{
  depositValue[t] >= 0 and
  withdrawalValue[t] >= 0 and
  balanceValue[t] >= 0
}

