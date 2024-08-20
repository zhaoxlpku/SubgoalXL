### Input
theorem amc12a_2002_p10:
  fixes a b :: real
  assumes h0 : "a\<noteq>0"
    and h1 : "b\<noteq>0"
    and h2 : "a/b = 2/1"
  shows "a/b = 6/3"

### Output
Given $a \neq 0$, $b \neq 0$, and $\frac{a}{b} = 2$, the objective $\frac{a}{b} = \frac{6}{3}$ is trivial because $\frac{6}{3} = 2$. The statement is $\boxed{bad}$.

---

### Input
theorem amc12a_2002_p10:
  fixes x :: real
  assumes "x\<noteq>7/5"
  shows "x\<noteq>7/5"

### Output
The assumption $x \neq \frac{7}{5}$ is the same as the objective, making it trivial and $\boxed{bad}$.

---

### Input
theorem amc12a_2002_p10:
  fixes x :: real
  assumes "x>0"
  shows "x^2 - x^2 = 17 \<Longrightarrow> x = 7 * sqrt 2"

### Output
The assumption $x^2 - x^2 = 17$ simplifies to $0 = 17$, which is a contradiction. Therefore, the statement is $\boxed{bad}$.

---

### Input
theorem amc12a_2002_p10:
  fixes x y :: real
  assumes h0 : "x - y = 15"
    and h1 : "x * y = 4"
  shows "x^2 + y^2 = 233"

### Output
Using $x - y = 15$ and $xy = 4$, we have $x^2 + y^2 = (x - y)^2 + 2xy = 225 + 8 = 233$. The statement is $\boxed{good}$.

---

### Input
theorem amc12a_2002_p10:
  fixes x y z :: real
  assumes h0 : "x + 2 * y - 2 * z + 1 = 0"
    and h1 : "2 * x + 4 * y - 4 * z + 5 = 0"
  shows "sqrt 2 / 2 = sqrt 2 / 2"

### Output
The assumptions $x + 2y - 2z + 1 = 0$ and $2x + 4y - 4z + 5 = 0$ are unrelated to the objective $\frac{\sqrt{2}}{2} = \frac{\sqrt{2}}{2}$, which is trivially true. The statement is $\boxed{bad}$.

---

### Input
theorem aime_2004_p1:
  fixes l w :: real
  assumes "l = 2 * w"
    and "2 * (l + w) = 60"
  shows "l * w = 200"

### Output
Given $l = 2w$ and $2(l + w) = 60$, we find $w = 10$ and $l = 20$. Therefore, $l \cdot w = 200$. The statement is $\boxed{good}$.

---

### Input
theorem amc12a_2002_p10:
  fixes x y :: real
  assumes h0 : "x>0"
    and h1 : "y>0"
    and h2 : "x\<noteq>y"
  shows "273 \<le> (273::nat)"

### Output
The assumptions $x > 0$, $y > 0$, and $x \neq y$ are unrelated to the objective $273 \leq 273$, which is trivially true. The statement is $\boxed{bad}$.

---

### Input
theorem amc12a_2002_p10:
  fixes x y z :: nat
  assumes h0 : "x + y + z = 1000"
    and h1 : "x \<le> 9"
    and h2 : "y \<le> 9"
    and h3 : "z \<le> 9"
  shows "x + y + z = 650"

### Output
Given $x + y + z = 1000$, $x \leq 9$, $y \leq 9$, and $z \leq 9$, the maximum $x + y + z$ is 27, far less than 1000. Therefore, the statement is $\boxed{bad}$.

---

### Input
theorem amc12a_2002_p10:
  fixes i :: complex
  assumes "i = \<i>"
  shows "((3 - 2 * i) * (3 - 2 * i)) = 5 - 12 * i"

### Output
Expanding $(3 - 2i)(3 - 2i)$ gives $9 - 12i + 4i^2 = 9 - 12i - 4 = 5 - 12i$. The statement is $\boxed{good}$.

---

### Input
theorem amc12a_2002_p10:
  fixes b :: real
  assumes "b^2 - 4 * 1 * 8 < 0"
  shows "b^2 - 4 * 1 * 8 < 0"

### Output
The assumption $b^2 - 4 \cdot 1 \cdot 8 < 0$ is the same as the objective, making it trivial and $\boxed{bad}$.

---

### Input
theorem amc12a_2002_p10:
  fixes x :: real
  assumes "abs (x + 5) = 20"
  shows "x^2 + 10 * x + 25 = 400"

### Output
The assumption $\text{abs}(x + 5) = 20$ leads to $x + 5 = 20$ or $x + 5 = -20$. Solving these, we get $x = 15$ or $x = -25$. Substituting these into $x^2 + 10x + 25$ results in $400$ in both cases. Thus, the statement is $\boxed{good}$.

---

### Input
theorem amc12a_2004_p10:
  fixes n :: nat
  assumes "n>0"
  shows "(\<Sum>d\<in>set (nat_to_list n). d) mod 10 = (\<Sum>d\<in>set (nat_to_list n). d) mod 10"

### Output
Given $n > 0$, the objective $(\sum d \in \text{set}(\text{nat\_to\_list } n). d) \mod 10 = (\sum d \in \text{set}(\text{nat\_to\_list } n). d) \mod 10$ is trivially true. The statement is $\boxed{bad}$.

---

### Input
theorem amc12a_2001_p1:
  fixes m b x y :: real
  assumes "y = m * x + b"
    and "m=-7"
    and "(x, y) = (3,0)"
  shows "m + b = 14"

### Output
Substituting $m = -7$, $x = 3$, and $y = 0$ into $y = mx + b$, we get $b = 21$. Thus, $m + b = 14$. The statement is $\boxed{good}$.

---

### Input
theorem amc12a_2002_p10:
  fixes x y :: real
  assumes h0 : "x = 3"
    and h1 : "y = 7"
    and h2 : "x = 5"
    and h3 : "y = 1"
  shows "x = 4 \<and> y = 4"

### Output
The assumptions $x = 3$ and $x = 5$, and $y = 7$ and $y = 1$, are contradictory. Therefore, the statement is $\boxed{bad}$.

---

### Input
theorem mathd_numbertheory_461:
  fixes m :: real
  assumes h0 : "m \<noteq>0"
    and h1 : "m + 1/m = 8"
  shows "m^2 + 1/(m^2) + 4 = 66"

### Output
Given $m + \frac{1}{m} = 8$, squaring gives $m^2 + 2 + \frac{1}{m^2} = 64$, so $m^2 + \frac{1}{m^2} = 62$. Adding 4 gives $66$. The statement is $\boxed{good}$.

---

### Input
theorem amc12a_2002_p10:
  fixes x y :: real
  assumes "x^2 + y^2 = -4 * x + 6 * y - 12"
  shows "sqrt 25 = 5"

### Output
The objective $\sqrt{25} = 5$ is trivially true and unrelated to the assumption $x^2 + y^2 = -4x + 6y - 12$, making the statement $\boxed{bad}$.

---

### Input
theorem amc12a_2009_p10:
  fixes a b c d :: real
  assumes h0 : "a + b = 1"
    and h1 : "a + d = 1"
    and h2 : "a + c = 1"
    and h3 : "a + b + c + d = 2"
  shows "a + c = 1"

### Output
The assumptions $a + b = 1$, $a + d = 1$, and $a + c = 1$ imply $b = c = d = 1 - a$. Substituting these into $a + b + c + d = 2$ gives $a + 3(1 - a) = 2 \implies a = \frac{1}{2}$. This confirms $a + c = 1$ but doesn't add new information, making the statement $\boxed{bad}$.

---

### Input
theorem mathd_numbertheory_492:
  fixes m :: nat
  assumes m:"m = 12"
  shows "m choose 4 = 495"

### Output
Given $m = 12$, $\binom{12}{4} = \frac{12 \times 11 \times 10 \times 9}{4 \times 3 \times 2 \times 1} = 495$. The statement is $\boxed{good}$.

---

### Input
theorem mathd_numbertheory_222:
  fixes y :: real
  shows "abs (y - 6) + 2 * y = 9 \<longrightarrow> y = 3"

### Output
For $y \geq 6$, $3y - 6 = 9 \implies y = 5$, which is not valid. For $y < 6$, $y + 6 = 9 \implies y = 3$, which is valid. Thus, $y = 3$. The statement is $\boxed{good}$.

---

### Input
theorem amc12a_2002_p10:
  fixes r :: real
  assumes "r>0"
  shows "(\<lambda>t. (r * cos t, r * sin t)) = (\<lambda>t. (r * cos t, r * sin t))"

### Output
Given $r > 0$, the objective $(\lambda t. (r \cos t, r \sin t)) = (\lambda t. (r \cos t, r \sin t))$ is trivially true. The statement is $\boxed{bad}$.

---

### Input
theorem amc12a_2002_p10:
  fixes t :: real
  assumes "t^2 + 4 * 10 = 0"
  shows "t^3 = 729"

### Output
The assumption $t^2 + 40 = 0$ has no real solutions, making the objective $t^3 = 729$ unprovable. The statement is $\boxed{bad}$.

---

### Input
theorem amc12a_2002_p10:
  fixes x :: real
  assumes "y = (x + 2) / (5 * x - 7)"
  shows "x = 7/5 \<Longrightarrow> y = 0"

### Output
Substituting $x = \frac{7}{5}$ into $y = \frac{x + 2}{5x - 7}$ results in division by zero. Therefore, the statement is $\boxed{bad}$.

---

### Input
theorem amc12a_2002_p10:
  fixes n :: nat
  assumes "n\<ge>1"
  shows "n mod 6 + 4 mod 7 \<le> 100 \<Longrightarrow> n mod 6 + 4 mod 7 \<le> 67"

### Output
Given $n \ge 1$, $n \mod 6 + 4 \mod 7$ ranges from 4 to 9, making both conditions trivially true. The statement is $\boxed{bad}$.