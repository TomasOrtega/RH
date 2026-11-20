import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
import Development.AutomorphicArithmetic.PrimitiveCosets.ToEBij

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost NumberField Ideal

section
variable {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]

/- English proof (translation)
Use `conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]`. Rewrite using `[Nat.prod_factorization_eq_prod_primeFactors, map_prod, Int.cast_prod]`. Unfold `primVal`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `p hp`.

Establish `hpp : p.Prime` using `Nat.prime_of_mem_primeFactors hp`. Establish `hi : n.factorization p ≠ 0`. Use `(Nat.support_factorization n ▸ hp : p ∈ n.factorization.support)` as an intermediate fact. Conclude with `Finsupp.mem_support_iff.1 this`. Rewrite using `[map_pow, Int.cast_pow]`.

Distinguish the cases in `hpc : p ∣ c`. Take `⟨h0, u, hu, hu1⟩` from `hram p hpp hpc`. Rewrite using `[cosetMean_of_nontrivial, h0, Int.cast_zero, zero_pow hi]`. Introduce `h`. Use `h _ ((mem_inertia_iff q d r p _).2 ⟨u, (mem_localUnits_iff p u).2 hu, rfl⟩)` as an intermediate fact.

Rewrite `this` using `[hψ, hu1]`. Evaluate the numerical expressions using `at this`. Establish `hcd : c ∣ ordCompl[p] N` using `Nat.dvd_ordCompl_of_dvd_not_dvd hc hpc`. Rewrite using `[cosetMean_of_trivial, AddChar.map_nsmul_eq_pow]`. Use `congr 1`.

Express the relevant statement in the definitionally equal form `ψ (Multiplicative.toAdd (r (frobUnit N p))) = _`. Rewrite using `[hψ, hF _ _ ((frobUnit_modEq hpp).1.of_dvd hcd)]`. Introduce `x hx`. Take `⟨u, hu, rfl⟩` from `(mem_inertia_iff q d r p _).1 hx`. Rewrite using `[hψ, hF _ _ (((mem_localUnits_iff p u).1 hu).of_dvd hcd), map_one, Int.cast_one]`.
-/
private theorem UpperTheory.GL.primVal_of_periodic {N c : ℕ} [NeZero N] (q d : ℕ)
    (r : (ZMod N)ˣ →* Multiplicative (E0 × A)) (ψ : AddChar (E0 × A) ℂ) (F : ℕ →* ℤ) (hc : c ∣ N)
    (hF : ∀ x y, x ≡ y [MOD c] → F x = F y)
    (hψ : ∀ u : (ZMod N)ˣ, ψ (Multiplicative.toAdd (r u)) = ((F (u : ZMod N).val : ℤ) : ℂ))
    (hram : ∀ p, p.Prime → p ∣ c → F p = 0 ∧
      ∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ 1 [MOD ordCompl[p] N] ∧ F (u : ZMod N).val = -1)
    (n : ℕ) (hn : n ≠ 0) : primVal (cftData q d r) ψ n = ((F n : ℤ) : ℂ) := by
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Nat.prod_factorization_eq_prod_primeFactors, map_prod, Int.cast_prod]
  unfold primVal
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hi : n.factorization p ≠ 0 := by
    have := (Nat.support_factorization n ▸ hp : p ∈ n.factorization.support)
    exact Finsupp.mem_support_iff.1 this
  rw [map_pow, Int.cast_pow]
  by_cases hpc : p ∣ c
  · obtain ⟨h0, u, hu, hu1⟩ := hram p hpp hpc
    rw [cosetMean_of_nontrivial, h0, Int.cast_zero, zero_pow hi]
    intro h
    have := h _ ((mem_inertia_iff q d r p _).2 ⟨u, (mem_localUnits_iff p u).2 hu, rfl⟩)
    rw [hψ, hu1] at this
    norm_num at this
  · have hcd : c ∣ ordCompl[p] N := Nat.dvd_ordCompl_of_dvd_not_dvd hc hpc
    rw [cosetMean_of_trivial, AddChar.map_nsmul_eq_pow]
    · congr 1
      change ψ (Multiplicative.toAdd (r (frobUnit N p))) = _
      rw [hψ, hF _ _ ((frobUnit_modEq hpp).1.of_dvd hcd)]
    · intro x hx
      obtain ⟨u, hu, rfl⟩ := (mem_inertia_iff q d r p _).1 hx
      rw [hψ, hF _ _ (((mem_localUnits_iff p u).1 hu).of_dvd hcd), map_one, Int.cast_one]

/- English proof (translation)
Apply `Nat.dvd_antisymm` to reduce the goal to its premises. Rewrite using `[← DirichletCharacter.mem_conductorSet_iff_conductor_dvd _ hc, DirichletCharacter.mem_conductorSet_iff, DirichletCharacter.factorsThrough_iff_ker_unitsMap hc]`. Introduce `u hu`. Rewrite `hu` using `[MonoidHom.mem_ker, unitsMap_eq_one_iff]`. Rewrite using `[MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, dirChar_unit, Units.val_one, hψ, hF _ _ hu, map_one, Int.cast_one]`.

Assume the negation of the conclusion as `hh`. Take `⟨u, hu, hu1⟩` from `hram`. Use `(inertia_conductor (H := A) N 0 0 r ψ c (NeZero.ne N) hp).2 hh _ ((mem_inertia_iff 0 0 r c _).2 ⟨u, (mem_localUnits_iff c u).2 hu, rfl⟩)` as an intermediate fact. Rewrite `this` using `[hψ, hu1]`. Evaluate the numerical expressions using `at this`.
-/
private theorem UpperTheory.GL.conductor_of_periodic {N c : ℕ} [NeZero N]
    (r : (ZMod N)ˣ →* Multiplicative (E0 × A)) (ψ : AddChar (E0 × A) ℂ) (F : ℕ →* ℤ) (hc : c ∣ N) (hp : c.Prime)
    (hF : ∀ x y, x ≡ y [MOD c] → F x = F y)
    (hψ : ∀ u : (ZMod N)ˣ, ψ (Multiplicative.toAdd (r u)) = ((F (u : ZMod N).val : ℤ) : ℂ))
    (hram : ∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ 1 [MOD ordCompl[c] N] ∧ F (u : ZMod N).val = -1) :
    (dirChar r ψ).conductor = c := by
  apply Nat.dvd_antisymm
  · rw [← DirichletCharacter.mem_conductorSet_iff_conductor_dvd _ hc,
      DirichletCharacter.mem_conductorSet_iff,
      DirichletCharacter.factorsThrough_iff_ker_unitsMap hc]
    intro u hu
    rw [MonoidHom.mem_ker, unitsMap_eq_one_iff] at hu
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, dirChar_unit, Units.val_one, hψ, hF _ _ hu,
      map_one, Int.cast_one]
  · by_contra hh
    obtain ⟨u, hu, hu1⟩ := hram
    have := (inertia_conductor (H := A) N 0 0 r ψ c (NeZero.ne N) hp).2 hh _
      ((mem_inertia_iff 0 0 r c _).2 ⟨u, (mem_localUnits_iff c u).2 hu, rfl⟩)
    rw [hψ, hu1] at this
    norm_num at this

end

private def UpperTheory.GL.jac (l : ℕ) : ℕ →* ℤ where
  toFun a := jacobiSym (a : ℤ) l
  map_one' := by simp
  map_mul' a b := by rw [Nat.cast_mul, jacobiSym.mul_left]

/- English proof (translation)
Establish `: Fact l.Prime` using `⟨hl⟩`. Establish `hN0` using `NeZero.ne N`. Establish `hcop : (ordProj[l] N).Coprime (ordCompl[l] N)` using `(Nat.coprime_ordCompl hl hN0).pow_left _`. Establish `hlP : l ∣ ordProj[l] N` using `Nat.dvd_ordProj_of_dvd hN0 hl hN`. Establish `: NeZero (ordProj[l] N)` using `⟨pow_ne_zero _ hl.ne_zero⟩`.

Take `⟨x, hx⟩` from `quadraticChar_exists_neg_one' (F := ZMod l) (by rwa [ZMod.ringChar_zmod_n])`. Take `⟨y, hy⟩` from `ZMod.unitsMap_surjective hlP x`. Take `⟨u, hu1, hu2⟩` from `exists_unit_crt (Nat.ordProj_mul_ordCompl_eq_self N l).symm hcop (Nat.ordProj_dvd N l) (Nat.ordCompl_dvd N l) y 1`. Use `⟨u, (unitsMap_eq_one_iff _ u).1 hu2, ?_⟩` and prove the remaining obligations. Establish `h3 : ZMod.unitsMap hN u = x`.

Rewrite using `[← hy, ← hu1, ← MonoidHom.comp_apply, ZMod.unitsMap_comp]`. Rewrite using `[← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast, ← hx, ← h3, ZMod.unitsMap_val, ZMod.natCast_val]`.
-/
private theorem UpperTheory.GL.exists_nonres {N l : ℕ} [NeZero N] (hl : l.Prime) (h2 : l ≠ 2) (hN : l ∣ N) :
    ∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ 1 [MOD ordCompl[l] N] ∧ jacobiSym ((u : ZMod N).val : ℤ) l = -1 := by
  have : Fact l.Prime := ⟨hl⟩
  have hN0 := NeZero.ne N
  have hcop : (ordProj[l] N).Coprime (ordCompl[l] N) := (Nat.coprime_ordCompl hl hN0).pow_left _
  have hlP : l ∣ ordProj[l] N := Nat.dvd_ordProj_of_dvd hN0 hl hN
  have : NeZero (ordProj[l] N) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨x, hx⟩ := quadraticChar_exists_neg_one' (F := ZMod l) (by rwa [ZMod.ringChar_zmod_n])
  obtain ⟨y, hy⟩ := ZMod.unitsMap_surjective hlP x
  obtain ⟨u, hu1, hu2⟩ := exists_unit_crt (Nat.ordProj_mul_ordCompl_eq_self N l).symm hcop
      (Nat.ordProj_dvd N l) (Nat.ordCompl_dvd N l) y 1
  refine ⟨u, (unitsMap_eq_one_iff _ u).1 hu2, ?_⟩
  have h3 : ZMod.unitsMap hN u = x := by
    rw [← hy, ← hu1, ← MonoidHom.comp_apply, ZMod.unitsMap_comp]
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast, ← hx, ← h3, ZMod.unitsMap_val,
    ZMod.natCast_val]

/- English proof (translation)
Rewrite using `[sgn2_toAdd_eq_ite]`. Apply the tactic sequence `rcases Int.units_eq_one_or s with rfl | rfl <;> simp`.
-/
private theorem UpperTheory.GL.sgn_val (s : ℤˣ) :
    (if Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 s) = 0 then (1 : ℂ) else -1) = (((s : ℤˣ) : ℤ) : ℂ) := by
  rw [sgn2_toAdd_eq_ite]
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp

/- English proof (translation)
Introduce `φ H`. Establish `hd` using `H.d_prime`. Establish `hq` using `H.q_prime`. Establish `ed` using `exists_nonres hd H.d_ne_two H.d_dvd_condN`. Establish `eq` using `exists_nonres hq H.q_ne_two H.q_dvd_condN`.

Establish `hch : ∀ u : (ZMod H.condN)ˣ, (chC : AddChar (E0 × φ.A) ℂ) (Multiplicative.toAdd (recH H.toHostRaw u)) = ((jac H.d (u : ZMod H.condN).val : ℤ) : ℂ)`. Introduce `u`. Express the relevant statement in the definitionally equal form `_ = ((jacobiSym _ _ : ℤ) : ℂ)`. Rewrite using `[← H.der.art_ch u]`. Conclude with `sgn_val _`.

Establish `one : ∀ l : ℕ, l.Prime → (∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD ordCompl[l] H.condN] ∧ jacobiSym ((u : ZMod H.condN).val : ℤ) l = -1) → ∀ p, p.Prime → p ∣ l → jac l p = 0 ∧ ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD ordCompl[p] H.condN] ∧ jac l (u : Z …`. Introduce `l hl e p hp hpl`. Take `rfl` from `(Nat.prime_dvd_prime_iff_eq hp hl).1 hpl`. Conclude with `⟨jac_self p hp.one_lt, e⟩`. Use `⟨conductor_of_periodic _ _ (jac H.d) H.d_dvd_condN hd (fun _ _ h => jacobi_congr h) hch ed, primVal_of_periodic _ _ _ _ (jac H.d) H.d_dvd_condN (fun _ _ h => jacobi_congr h) hch (one _ hd ed), fun hP => ?_⟩` and prove the remaining obligations.

Establish `hps : ∀ u : (ZMod H.condN)ˣ, (psC : AddChar (E0 × φ.A) ℂ) (Multiplicative.toAdd (recH H.toHostRaw u)) = ((jac H.q (u : ZMod H.condN).val : ℤ) : ℂ)`. Introduce `u`. Express the relevant statement in the definitionally equal form `_ = ((jacobiSym _ _ : ℤ) : ℂ)`. Rewrite using `[← hP u]`. Conclude with `sgn_val _`.

Use `⟨conductor_of_periodic _ _ (jac H.q) H.q_dvd_condN hq (fun _ _ h => jacobi_congr h) hps eq, primVal_of_periodic _ _ _ _ (jac H.q) H.q_dvd_condN (fun _ _ h => jacobi_congr h) hps (one _ hq eq), ?_⟩` and prove the remaining obligations. Use `primVal_of_periodic (c := H.d * H.q) _ _ _ _ (jac H.d * jac H.q) (H.coprime_q_d.symm.mul_dvd_of_dvd_of_dvd H.d_dvd_condN H.q_dvd_condN) (fun x y h => ?_) (fun u => ?_) ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `jacobiSym _ _ * jacobiSym _ _ = jacobiSym _ _ * jacobiSym _ _`. Rewrite using `[jacobi_congr (h.of_dvd (dvd_mul_right _ _)), jacobi_congr (h.of_dvd (dvd_mul_left _ _))]`. Unfold `chpsC`.

Rewrite using `[AddChar.mul_apply, hch, hps, MonoidHom.mul_apply, Int.cast_mul]`. Introduce `p hp hpl`. Break down `hp.dvd_mul.1 hpl with h | h` into its components or cases. Take `rfl` from `(Nat.prime_dvd_prime_iff_eq hp hd).1 h`. Take `⟨u, hu, hu1⟩` from `ed`.

Establish `hqd : H.q ∣ ordCompl[H.d] H.condN` using `Nat.dvd_ordCompl_of_dvd_not_dvd H.q_dvd_condN (fun hh => H.q_ne_d ((Nat.prime_dvd_prime_iff_eq hd hq).1 hh).symm)`. Use `⟨?_, u, hu, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `jacobiSym _ _ * jacobiSym _ _ = 0`. Rewrite using `[jac_self _ hd.one_lt, zero_mul]`. Express the relevant statement in the definitionally equal form `jacobiSym _ _ * jacobiSym _ _ = -1`.

Rewrite using `[hu1, jacobi_congr (hu.of_dvd hqd)]`. Simplify using the standard rewrite rules. Take `rfl` from `(Nat.prime_dvd_prime_iff_eq hp hq).1 h`. Take `⟨u, hu, hu1⟩` from `eq`. Establish `hqd : H.d ∣ ordCompl[H.q] H.condN` using `Nat.dvd_ordCompl_of_dvd_not_dvd H.d_dvd_condN (fun hh => H.q_ne_d ((Nat.prime_dvd_prime_iff_eq hq hd).1 hh))`.

Use `⟨?_, u, hu, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `jacobiSym _ _ * jacobiSym _ _ = 0`. Rewrite using `[jac_self _ hq.one_lt, mul_zero]`. Express the relevant statement in the definitionally equal form `jacobiSym _ _ * jacobiSym _ _ = -1`. Rewrite using `[hu1, jacobi_congr (hu.of_dvd hqd)]`.

Simplify using the standard rewrite rules.
-/
theorem UpperTheory.GL.ch_cond :
    ∀ {φ : Frame} (H : HostAx φ), (dirChar (recH H.toHostRaw) chC).conductor = H.d ∧
      (∀ n : ℕ, n ≠ 0 → primVal (arith H.toHostRaw) chC n = ((jacobiSym (n : ℤ) H.d : ℤ) : ℂ)) ∧
      (H.PsQ → (dirChar (recH H.toHostRaw) psC).conductor = H.q ∧
        (∀ n : ℕ, n ≠ 0 → primVal (arith H.toHostRaw) psC n = ((jacobiSym (n : ℤ) H.q : ℤ) : ℂ)) ∧
        ∀ n : ℕ, n ≠ 0 → primVal (arith H.toHostRaw) chpsC n = ((jacobiSym (n : ℤ) H.d * jacobiSym (n : ℤ) H.q : ℤ) : ℂ)) := by
  intro φ H
  have hd := H.d_prime
  have hq := H.q_prime
  have ed := exists_nonres hd H.d_ne_two H.d_dvd_condN
  have eq := exists_nonres hq H.q_ne_two H.q_dvd_condN
  have hch : ∀ u : (ZMod H.condN)ˣ, (chC : AddChar (E0 × φ.A) ℂ) (Multiplicative.toAdd (recH H.toHostRaw u))
      = ((jac H.d (u : ZMod H.condN).val : ℤ) : ℂ) := by
    intro u
    change _ = ((jacobiSym _ _ : ℤ) : ℂ)
    rw [← H.der.art_ch u]
    exact sgn_val _
  have one : ∀ l : ℕ, l.Prime → (∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD ordCompl[l] H.condN] ∧
      jacobiSym ((u : ZMod H.condN).val : ℤ) l = -1) → ∀ p, p.Prime → p ∣ l → jac l p = 0 ∧
      ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD ordCompl[p] H.condN] ∧
        jac l (u : ZMod H.condN).val = -1 := by
    intro l hl e p hp hpl
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hl).1 hpl
    exact ⟨jac_self p hp.one_lt, e⟩
  refine ⟨conductor_of_periodic _ _ (jac H.d) H.d_dvd_condN hd (fun _ _ h => jacobi_congr h) hch ed,
    primVal_of_periodic _ _ _ _ (jac H.d) H.d_dvd_condN (fun _ _ h => jacobi_congr h) hch (one _ hd ed), fun hP => ?_⟩
  have hps : ∀ u : (ZMod H.condN)ˣ, (psC : AddChar (E0 × φ.A) ℂ) (Multiplicative.toAdd (recH H.toHostRaw u))
      = ((jac H.q (u : ZMod H.condN).val : ℤ) : ℂ) := by
    intro u
    change _ = ((jacobiSym _ _ : ℤ) : ℂ)
    rw [← hP u]
    exact sgn_val _
  refine ⟨conductor_of_periodic _ _ (jac H.q) H.q_dvd_condN hq (fun _ _ h => jacobi_congr h) hps eq,
    primVal_of_periodic _ _ _ _ (jac H.q) H.q_dvd_condN (fun _ _ h => jacobi_congr h) hps (one _ hq eq), ?_⟩
  refine primVal_of_periodic (c := H.d * H.q) _ _ _ _ (jac H.d * jac H.q)
    (H.coprime_q_d.symm.mul_dvd_of_dvd_of_dvd H.d_dvd_condN H.q_dvd_condN) (fun x y h => ?_) (fun u => ?_) ?_
  · change jacobiSym _ _ * jacobiSym _ _ = jacobiSym _ _ * jacobiSym _ _
    rw [jacobi_congr (h.of_dvd (dvd_mul_right _ _)), jacobi_congr (h.of_dvd (dvd_mul_left _ _))]
  · unfold chpsC
    rw [AddChar.mul_apply, hch, hps, MonoidHom.mul_apply, Int.cast_mul]
  · intro p hp hpl
    rcases hp.dvd_mul.1 hpl with h | h
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hd).1 h
      obtain ⟨u, hu, hu1⟩ := ed
      have hqd : H.q ∣ ordCompl[H.d] H.condN := Nat.dvd_ordCompl_of_dvd_not_dvd H.q_dvd_condN
        (fun hh => H.q_ne_d ((Nat.prime_dvd_prime_iff_eq hd hq).1 hh).symm)
      refine ⟨?_, u, hu, ?_⟩
      · change jacobiSym _ _ * jacobiSym _ _ = 0
        rw [jac_self _ hd.one_lt, zero_mul]
      · change jacobiSym _ _ * jacobiSym _ _ = -1
        rw [hu1, jacobi_congr (hu.of_dvd hqd)]
        simp
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hq).1 h
      obtain ⟨u, hu, hu1⟩ := eq
      have hqd : H.d ∣ ordCompl[H.q] H.condN := Nat.dvd_ordCompl_of_dvd_not_dvd H.d_dvd_condN
        (fun hh => H.q_ne_d ((Nat.prime_dvd_prime_iff_eq hq hd).1 hh))
      refine ⟨?_, u, hu, ?_⟩
      · change jacobiSym _ _ * jacobiSym _ _ = 0
        rw [jac_self _ hq.one_lt, mul_zero]
      · change jacobiSym _ _ * jacobiSym _ _ = -1
        rw [hu1, jacobi_congr (hu.of_dvd hqd)]
        simp
