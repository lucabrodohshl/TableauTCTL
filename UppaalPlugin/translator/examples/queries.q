E<> p0.crit
E<> (p0.crit && p1.crit)
E<> (p0.idle && p0.crit)
A[] (p0.idle || p0.wait || p0.crit)
p0.wait --> p0.crit
E<> (gclk > 4 && gclk < 5)
E<> (counter == 7)
A[] not deadlock
Pr[<=10](<> p0.crit)
sup{p0.crit}: gclk
