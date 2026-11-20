import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Take `⟨y, rfl⟩ : ∃ y, x = y + 1` from `⟨x - 1, by omega⟩`. Use `geom_sum_mul_add y l` as an intermediate fact. Simplify using `only [Nat.add_sub_cancel]`. Use linear arithmetic over natural numbers and integers.
-/
private lemma geo_mul (x l : ℕ) (hx : 1 ≤ x) :
    (∑ i ∈ Finset.range l, x ^ i) * (x - 1) = x ^ l - 1 := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  have := geom_sum_mul_add y l
  simp only [Nat.add_sub_cancel]
  omega

/- English proof (translation)
Take `⟨c, rfl⟩` from `hb`. Rewrite using `[Nat.mul_div_cancel_left c hb0]`. Substitute `hS` using the available equality. Rewrite using `[show S * a * c = a * (S * c) by ring, Nat.mul_div_cancel_left _ ha]`.
-/
private lemma div_id (N a b S : ℕ) (ha : 0 < a) (hS : S * a = b) (hb : b ∣ N) (hb0 : 0 < b) :
    S * (N / b) = N / a := by
  obtain ⟨c, rfl⟩ := hb
  rw [Nat.mul_div_cancel_left c hb0]
  subst hS
  rw [show S * a * c = a * (S * c) by ring, Nat.mul_div_cancel_left _ ha]

/- English proof (translation)
Simplify using `using Nat.sub_dvd_pow_sub_pow x 1 e`.
-/
private lemma sub_one_dvd (x e : ℕ) : x - 1 ∣ x ^ e - 1 := by
  simpa using Nat.sub_dvd_pow_sub_pow x 1 e

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Multiset.range_succ, Multiset.map_cons, Finset.sum_range_succ, ih, add_comm, Multiset.singleton_add]`.
-/
private lemma ms_sum {α : Type*} (n : ℕ) (g : ℕ → α) :
    (Multiset.range n).map g = ∑ j ∈ Finset.range n, ({g j} : Multiset α) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Multiset.range_succ, Multiset.map_cons, Finset.sum_range_succ, ih, add_comm,
      Multiset.singleton_add]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]`. Simplify using the standard rewrite rules.
-/
private lemma list_sum {α : Type*} (l : ℕ) (F : ℕ → Multiset α) :
    ((List.range l).map F).sum = ∑ i ∈ Finset.range l, F i := by
  induction l with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/- English proof (translation)
Proceed by induction on `m' with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ih, Nat.mul_succ, Finset.sum_range_add]`.

Use `congr 1`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [Nat.add_comm]`.
-/
private lemma block_mul {α : Type*} (l m' : ℕ) (g : ℕ → α) :
    ∑ i ∈ Finset.range l, ∑ j ∈ Finset.range m', ({g (i + l * j)} : Multiset α) =
      ∑ n ∈ Finset.range (l * m'), ({g n} : Multiset α) := by
  induction m' with
  | zero => simp
  | succ m ih =>
    calc ∑ i ∈ Finset.range l, ∑ j ∈ Finset.range (m + 1), ({g (i + l * j)} : Multiset α)
        = ∑ i ∈ Finset.range l, (∑ j ∈ Finset.range m, ({g (i + l * j)} : Multiset α) +
            {g (i + l * m)}) := Finset.sum_congr rfl fun i _ => Finset.sum_range_succ _ m
      _ = ∑ i ∈ Finset.range l, ∑ j ∈ Finset.range m, ({g (i + l * j)} : Multiset α) +
            ∑ i ∈ Finset.range l, ({g (i + l * m)} : Multiset α) := Finset.sum_add_distrib
      _ = ∑ n ∈ Finset.range (l * (m + 1)), ({g n} : Multiset α) := by
          rw [ih, Nat.mul_succ, Finset.sum_range_add]
          congr 1
          exact Finset.sum_congr rfl fun i _ => by rw [Nat.add_comm]

/- English proof (translation)
Establish `hper : Function.Periodic G m` using `hG`. Establish `hinj : Set.InjOn (fun j => l * j % m) (Finset.range m : Set ℕ)`. Introduce `x hx y hy hxy`. Establish `hx' : x < m` using `by simpa using hx`. Establish `hy' : y < m` using `by simpa using hy`.

Establish `h1 : l * x ≡ l * y [MOD m]` using `hxy`. Establish `h2 : x ≡ y [MOD m]` using `Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hc) h1`. Conclude with `Nat.ModEq.eq_of_lt_of_lt h2 hx' hy'`. Establish `himg : (Finset.range m).image (fun j => l * j % m) = Finset.range m`. Apply `Finset.eq_of_subset_of_card_le` to reduce the goal to its premises.

Introduce `x hx`. Take `⟨y, -, rfl⟩` from `Finset.mem_image.1 hx`. Conclude with `Finset.mem_range.2 (Nat.mod_lt _ hm)`. Rewrite using `[Finset.card_image_of_injOn hinj]`. Rewrite using `[ms_sum, ms_sum]`.

Use `conv_rhs => rw [← himg]`. Rewrite using `[Finset.sum_image hinj]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [hper.map_mod_nat]`.
-/
private lemma perm_map {α : Type*} (l m : ℕ) (hc : Nat.Coprime l m) (hm : 0 < m) (G : ℕ → α)
    (hG : ∀ n, G (n + m) = G n) :
    (Multiset.range m).map (fun j => G (l * j)) = (Multiset.range m).map G := by
  have hper : Function.Periodic G m := hG
  have hinj : Set.InjOn (fun j => l * j % m) (Finset.range m : Set ℕ) := by
    intro x hx y hy hxy
    have hx' : x < m := by simpa using hx
    have hy' : y < m := by simpa using hy
    have h1 : l * x ≡ l * y [MOD m] := hxy
    have h2 : x ≡ y [MOD m] := Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hc) h1
    exact Nat.ModEq.eq_of_lt_of_lt h2 hx' hy'
  have himg : (Finset.range m).image (fun j => l * j % m) = Finset.range m := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_range.2 (Nat.mod_lt _ hm)
    · rw [Finset.card_image_of_injOn hinj]
  rw [ms_sum, ms_sum]
  conv_rhs => rw [← himg]
  rw [Finset.sum_image hinj]
  exact Finset.sum_congr rfl fun j _ => by rw [hper.map_mod_nat]

private def lbk (Q q : ℕ) (p : ℕ × ℕ) : Multiset (ℕ × ZMod (Q - 1)) :=
  (Multiset.range p.1).map fun j =>
    ((1 : ℕ), ((p.2 * q ^ j * ((Q - 1) / (q ^ p.1 - 1)) : ℕ) : ZMod (Q - 1)))

/- English proof (translation)
Use `set G : ℕ → ℕ × ZMod (Q - 1) := fun j => ((1 : ℕ), ((k * q ^ j * ((Q - 1) / (q ^ (l * m') - 1)) : ℕ) : ZMod (Q - 1))) with hGdef`. Establish `h1 : ∀ i, lbk Q (q ^ l) (m', k * q ^ i) = ∑ j ∈ Finset.range m', ({G (i + l * j)} : Multiset _)`. Introduce `i`. Rewrite using `[← ms_sum (n := m') (g := fun j => G (i + l * j))]`. Unfold `lbk`.

Use `Multiset.map_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [hGdef, ← pow_mul, pow_add, mul_assoc]`. Establish `h2 : lbk Q q (l * m', k) = (Multiset.range (l * m')).map G` using `rfl`. Rewrite using `[list_sum, h2, ms_sum, ← block_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => h1 i`.
-/
private lemma lbk_dvd (Q q l m' k : ℕ) :
    ((List.range l).map fun i => lbk Q (q ^ l) (m', k * q ^ i)).sum = lbk Q q (l * m', k) := by
  set G : ℕ → ℕ × ZMod (Q - 1) := fun j =>
    ((1 : ℕ), ((k * q ^ j * ((Q - 1) / (q ^ (l * m') - 1)) : ℕ) : ZMod (Q - 1))) with hGdef
  have h1 : ∀ i, lbk Q (q ^ l) (m', k * q ^ i) =
      ∑ j ∈ Finset.range m', ({G (i + l * j)} : Multiset _) := by
    intro i
    rw [← ms_sum (n := m') (g := fun j => G (i + l * j))]
    unfold lbk
    refine Multiset.map_congr rfl fun j _ => ?_
    simp only [hGdef, ← pow_mul, pow_add, mul_assoc]
  have h2 : lbk Q q (l * m', k) = (Multiset.range (l * m')).map G := rfl
  rw [list_sum, h2, ms_sum, ← block_mul]
  exact Finset.sum_congr rfl fun i _ => h1 i

/- English proof (translation)
Establish `hqm : 1 < q ^ m` using `Nat.one_lt_pow hm.ne' (by omega)`. Establish `hql : 1 < (q ^ l) ^ m` using `Nat.one_lt_pow hm.ne' (Nat.one_lt_pow hl.ne_zero (by omega))`. Establish `hT : (∑ i ∈ Finset.range l, q ^ (m * i)) * (q ^ m - 1) = (q ^ l) ^ m - 1`. Use `geo_mul (q ^ m) l hqm.le` as an intermediate fact. Simplify using `only [← pow_mul] at this ⊢`.

Rewrite using `[this, Nat.mul_comm l m]`. Establish `hd1 : (q ^ l) ^ m - 1 ∣ Q - 1`. Take `⟨e, rfl⟩` from `hmf`. Rewrite using `[hQ, pow_mul]`. Conclude with `sub_one_dvd _ e`.

Establish `hd2 : q ^ m - 1 ∣ Q - 1` using `(Dvd.intro_left _ hT).trans hd1`. Establish `hC` using `div_id (Q - 1) (q ^ m - 1) ((q ^ l) ^ m - 1) _ (by omega) hT hd1 (by omega)`. Establish `hC2 : (Q - 1) / (q ^ m - 1) * (q ^ m - 1) = Q - 1` using `Nat.div_mul_cancel hd2`. Use `set C := (Q - 1) / (q ^ m - 1) with hCdef`. Use `set T := ∑ i ∈ Finset.range l, q ^ (m * i) with hTdef`.

Use `set G : ℕ → ℕ × ZMod (Q - 1) := fun j => ((1 : ℕ), ((k * q ^ j * C : ℕ) : ZMod (Q - 1))) with hGdef`. Establish `hG : ∀ n, G (n + m) = G n`. Introduce `n`. Take `⟨u, hu⟩ : ∃ u, q ^ m = u + 1` from `⟨q ^ m - 1, by omega⟩`. Establish `hCu : C * u = Q - 1` using `by rw [hu] at hC2; simpa using hC2`.

Establish `: k * q ^ (n + m) * C = k * q ^ n * C + k * q ^ n * (Q - 1)`. Rewrite using `[pow_add, hu, ← hCu]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hGdef, this]`. Move the coercions through the operations in `[ZMod.natCast_self]`.

Simplify using `[ZMod.natCast_self]`. Establish `hL : lbk Q (q ^ l) (m, k * T) = (Multiset.range m).map fun j => G (l * j)`. Unfold `lbk`. Use `Multiset.map_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [hGdef]`.

Rewrite using `[← hC, pow_mul]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hL, perm_map l m ((Nat.Prime.coprime_iff_not_dvd hl).2 hnd) hm G hG]`. Both sides reduce to the same expression.
-/
private lemma lbk_ndvd (Q q l f m k : ℕ) (hq : 2 ≤ q) (hl : l.Prime) (hQ : Q = (q ^ l) ^ f)
    (hm : 0 < m) (hmf : m ∣ f) (hnd : ¬ l ∣ m) :
    lbk Q (q ^ l) (m, k * ∑ i ∈ Finset.range l, q ^ (m * i)) = lbk Q q (m, k) := by
  have hqm : 1 < q ^ m := Nat.one_lt_pow hm.ne' (by omega)
  have hql : 1 < (q ^ l) ^ m := Nat.one_lt_pow hm.ne' (Nat.one_lt_pow hl.ne_zero (by omega))
  have hT : (∑ i ∈ Finset.range l, q ^ (m * i)) * (q ^ m - 1) = (q ^ l) ^ m - 1 := by
    have := geo_mul (q ^ m) l hqm.le
    simp only [← pow_mul] at this ⊢
    rw [this, Nat.mul_comm l m]
  have hd1 : (q ^ l) ^ m - 1 ∣ Q - 1 := by
    obtain ⟨e, rfl⟩ := hmf
    rw [hQ, pow_mul]
    exact sub_one_dvd _ e
  have hd2 : q ^ m - 1 ∣ Q - 1 := (Dvd.intro_left _ hT).trans hd1
  have hC := div_id (Q - 1) (q ^ m - 1) ((q ^ l) ^ m - 1) _ (by omega) hT hd1 (by omega)
  have hC2 : (Q - 1) / (q ^ m - 1) * (q ^ m - 1) = Q - 1 := Nat.div_mul_cancel hd2
  set C := (Q - 1) / (q ^ m - 1) with hCdef
  set T := ∑ i ∈ Finset.range l, q ^ (m * i) with hTdef
  set G : ℕ → ℕ × ZMod (Q - 1) := fun j => ((1 : ℕ), ((k * q ^ j * C : ℕ) : ZMod (Q - 1))) with hGdef
  have hG : ∀ n, G (n + m) = G n := by
    intro n
    obtain ⟨u, hu⟩ : ∃ u, q ^ m = u + 1 := ⟨q ^ m - 1, by omega⟩
    have hCu : C * u = Q - 1 := by rw [hu] at hC2; simpa using hC2
    have : k * q ^ (n + m) * C = k * q ^ n * C + k * q ^ n * (Q - 1) := by
      rw [pow_add, hu, ← hCu]; ring
    simp only [hGdef, this]
    push_cast [ZMod.natCast_self]
    simp [ZMod.natCast_self]
  have hL : lbk Q (q ^ l) (m, k * T) = (Multiset.range m).map fun j => G (l * j) := by
    unfold lbk
    refine Multiset.map_congr rfl fun j _ => ?_
    simp only [hGdef]
    rw [← hC, pow_mul]
    congr 2
    ring
  rw [hL, perm_map l m ((Nat.Prime.coprime_iff_not_dvd hl).2 hnd) hm G hG]
  rfl

/- English proof (translation)
Introduce `L`. Proceed by induction on `L with`. Consider the case `nil => intro _ _`. Simplify using `[liftAll]`. Consider the case `cons p L ih`.

Introduce `h0 hd`. Take `⟨m, k⟩` from `p`. Establish `hsplit : liftAll q l ((m, k) :: L) = (if l ∣ m then liftL q l [(m, k)] else [(m, k * ∑ i ∈ Finset.range l, q ^ (m * i))]) ++ liftAll q l L`. Simplify using `[liftAll]`. Rewrite `hd`, the goal using `[hsplit]`.

Establish `hdL : ∀ p ∈ liftAll q l L, p.1 ∣ f` using `fun p hp => hd p (List.mem_append_right _ hp)`. Rewrite using `[List.map_append, List.sum_append, ih (fun p hp => h0 p (List.mem_cons_of_mem _ hp)) hdL, List.map_cons, List.sum_cons]`. Use `congr 1`. Distinguish the cases in `hlm : l ∣ m`. Take `⟨m', rfl⟩` from `hlm`.

Establish `: liftL q l [(l * m', k)] = (List.range l).map fun i => (m', k * q ^ i)`. Simplify using `[liftL, Nat.mul_div_cancel_left _ hl.pos]`. Rewrite using `[if_pos (dvd_mul_right _ _), this, List.map_map]`. Conclude with `lbk_dvd Q q l m' k`. Rewrite `hd`, the goal using `[if_neg hlm]`.

Establish `hmf : m ∣ f` using `hd (m, _) (List.mem_append_left _ (List.mem_singleton.2 rfl))`. Simplify using `using lbk_ndvd Q q l f m k hq hl hQ (h0 (m, k) List.mem_cons_self) hmf hlm`.
-/
private lemma lbkL (Q q l f : ℕ) (hq : 2 ≤ q) (hl : l.Prime) (hQ : Q = (q ^ l) ^ f) :
    ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1) → (∀ p ∈ liftAll q l L, p.1 ∣ f) →
      ((liftAll q l L).map (lbk Q (q ^ l))).sum = (L.map (lbk Q q)).sum := by
  intro L
  induction L with
  | nil => intro _ _; simp [liftAll]
  | cons p L ih =>
    intro h0 hd
    obtain ⟨m, k⟩ := p
    have hsplit : liftAll q l ((m, k) :: L) = (if l ∣ m then liftL q l [(m, k)] else
        [(m, k * ∑ i ∈ Finset.range l, q ^ (m * i))]) ++ liftAll q l L := by
      simp [liftAll]
    rw [hsplit] at hd ⊢
    have hdL : ∀ p ∈ liftAll q l L, p.1 ∣ f := fun p hp => hd p (List.mem_append_right _ hp)
    rw [List.map_append, List.sum_append, ih (fun p hp => h0 p (List.mem_cons_of_mem _ hp)) hdL,
      List.map_cons, List.sum_cons]
    congr 1
    by_cases hlm : l ∣ m
    · obtain ⟨m', rfl⟩ := hlm
      have : liftL q l [(l * m', k)] = (List.range l).map fun i => (m', k * q ^ i) := by
        simp [liftL, Nat.mul_div_cancel_left _ hl.pos]
      rw [if_pos (dvd_mul_right _ _), this, List.map_map]
      exact lbk_dvd Q q l m' k
    · rw [if_neg hlm] at hd ⊢
      have hmf : m ∣ f := hd (m, _) (List.mem_append_left _ (List.mem_singleton.2 rfl))
      simpa using lbk_ndvd Q q l f m k hq hl hQ (h0 (m, k) List.mem_cons_self) hmf hlm

/- English proof (translation)
Introduce and unpack `⟨m, k⟩ hp`. Distinguish the cases in `hlm : l ∣ m`. Establish `h1 : (m / l, k * q ^ 0) ∈ liftAll q l L`. Use `List.mem_flatMap.2 ⟨(m, k), hp, ?_⟩` and prove the remaining obligations. Simplify using `only [if_pos hlm, liftL]`.

Simplify using `only [List.flatMap_cons, List.flatMap_nil, List.append_nil]`. Conclude with `List.mem_map.2 ⟨0, List.mem_range.2 hl.pos, rfl⟩`. Establish `h2` using `hd _ h1`. Take `⟨m', rfl⟩` from `hlm`. Rewrite `h2` using `[Nat.mul_div_cancel_left _ hl.pos]`.

Conclude with `Nat.mul_dvd_mul_left l h2`. Establish `h1 : (m, k * ∑ i ∈ Finset.range l, q ^ (m * i)) ∈ liftAll q l L`. Use `List.mem_flatMap.2 ⟨(m, k), hp, ?_⟩` and prove the remaining obligations. Simplify using `[if_neg hlm]`. Conclude with `(hd _ h1).mul_left l`.
-/
private lemma splitsL (q l f : ℕ) (hl : l.Prime) (L : List (ℕ × ℕ))
    (hd : ∀ p ∈ liftAll q l L, p.1 ∣ f) : ∀ p ∈ L, p.1 ∣ l * f := by
  rintro ⟨m, k⟩ hp
  by_cases hlm : l ∣ m
  · have h1 : (m / l, k * q ^ 0) ∈ liftAll q l L := by
      refine List.mem_flatMap.2 ⟨(m, k), hp, ?_⟩
      simp only [if_pos hlm, liftL]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact List.mem_map.2 ⟨0, List.mem_range.2 hl.pos, rfl⟩
    have h2 := hd _ h1
    obtain ⟨m', rfl⟩ := hlm
    rw [Nat.mul_div_cancel_left _ hl.pos] at h2
    exact Nat.mul_dvd_mul_left l h2
  · have h1 : (m, k * ∑ i ∈ Finset.range l, q ^ (m * i)) ∈ liftAll q l L := by
      refine List.mem_flatMap.2 ⟨(m, k), hp, ?_⟩
      simp [if_neg hlm]
    exact (hd _ h1).mul_left l

/- English proof (translation)
Introduce `a l Q hl ha hs`. Take `⟨q, D, L⟩` from `a`. Take `⟨hq, hD, hL⟩` from `ha`. Take `⟨f, hf, hQ, hdiv⟩` from `hs`. Establish `hq' : 2 ≤ q` using `hq`.

Establish `hQ' : Q = (q ^ l) ^ f` using `hQ`. Establish `hdiv' : ∀ p ∈ liftAll q l L, p.1 ∣ f` using `hdiv`. Establish `hL0 : ∀ p ∈ L, 0 < p.1` using `fun p hp => (hL p hp).1`. Use `⟨⟨l * f, Nat.mul_pos hl.pos hf, by rw [hQ', pow_mul], splitsL q l f hl L hdiv'⟩, ?_⟩` and prove the remaining obligations. Establish `hS` using `geo_mul q l (by omega)`.

Establish `hql : 1 < q ^ l` using `Nat.one_lt_pow hl.ne_zero (by omega)`. Establish `hDid : (∑ i ∈ Finset.range l, q ^ i) * ((Q - 1) / (q ^ l - 1)) = (Q - 1) / (q - 1)` using `div_id (Q - 1) (q - 1) (q ^ l - 1) _ (by omega) hS (by rw [hQ']; exact sub_one_dvd _ f) (by omega)`. Establish `hDpart : ((⟨q, D, L⟩ : Lbl).lift l).D.map (fun p => (p.1, ((p.2 * ((Q - 1) / (((⟨q, D, L⟩ : Lbl).lift l).q - 1)) : ℕ) : ZMod (Q - 1)))) = D.map (fun p => (p.1, ((p.2 * ((Q - 1) / (q - 1)) : ℕ) : ZMod (Q - 1))))` using `by show (D.map _).map _ = _`. Rewrite using `[List.map_map]`. Use `List.map_congr_left fun p _ => ?_` and prove the remaining obligations.

Simplify using `only [Function.comp]`. Rewrite using `[← hDid, mul_assoc]`. Both sides reduce to the same expression. Establish `hLpart` using `lbkL Q q l f hq' hl hQ' L hL0 hdiv'`. Unfold `Lbl.blocks`.

Rewrite using `[hDpart]`. Use `congr 1`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.liftBlocks :
    LiftBlocks := by
  intro a l Q hl ha hs
  obtain ⟨q, D, L⟩ := a
  obtain ⟨hq, hD, hL⟩ := ha
  obtain ⟨f, hf, hQ, hdiv⟩ := hs
  have hq' : 2 ≤ q := hq
  have hQ' : Q = (q ^ l) ^ f := hQ
  have hdiv' : ∀ p ∈ liftAll q l L, p.1 ∣ f := hdiv
  have hL0 : ∀ p ∈ L, 0 < p.1 := fun p hp => (hL p hp).1
  refine ⟨⟨l * f, Nat.mul_pos hl.pos hf, by rw [hQ', pow_mul], splitsL q l f hl L hdiv'⟩, ?_⟩
  have hS := geo_mul q l (by omega)
  have hql : 1 < q ^ l := Nat.one_lt_pow hl.ne_zero (by omega)
  have hDid : (∑ i ∈ Finset.range l, q ^ i) * ((Q - 1) / (q ^ l - 1)) = (Q - 1) / (q - 1) :=
    div_id (Q - 1) (q - 1) (q ^ l - 1) _ (by omega) hS (by rw [hQ']; exact sub_one_dvd _ f) (by omega)
  have hDpart : ((⟨q, D, L⟩ : Lbl).lift l).D.map (fun p =>
        (p.1, ((p.2 * ((Q - 1) / (((⟨q, D, L⟩ : Lbl).lift l).q - 1)) : ℕ) : ZMod (Q - 1)))) =
      D.map (fun p => (p.1, ((p.2 * ((Q - 1) / (q - 1)) : ℕ) : ZMod (Q - 1)))) := by
    show (D.map _).map _ = _
    rw [List.map_map]
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp]
    rw [← hDid, mul_assoc]
    rfl
  have hLpart := lbkL Q q l f hq' hl hQ' L hL0 hdiv'
  unfold Lbl.blocks
  rw [hDpart]
  congr 1
