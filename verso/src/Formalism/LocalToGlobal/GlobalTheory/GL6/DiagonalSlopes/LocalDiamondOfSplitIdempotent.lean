import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.ComplexSpanBlockActionStable
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.CharacterFiniteLevelZeroOfForms
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.ComplementSmulLocalExtensionMatrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

open NumberField IsDedekindDomain Formalism.UG Classical Matrix Formalism.BasicNotions Formalism.L2.Forms
open scoped TensorProduct

section Prime

/- English proof (translation)
Establish `: Finite G` using `Nat.finite_of_card_ne_zero (by rw [hG]; exact hp.ne_zero)`. Establish `hd : Nat.card H ∣ p` using `hG ▸ AddSubgroup.card_addSubgroup_dvd_card H`. Break down `(Nat.dvd_prime hp).1 hd with h | h` into its components or cases. Conclude with `absurd (AddSubgroup.mem_bot.1 ((AddSubgroup.eq_bot_of_card_eq H h) ▸ hy)) hy0`. Conclude with `AddSubgroup.eq_top_of_card_eq H (h.trans hG.symm)`.
-/
theorem subgroup_prime_card_eq_top {G : Type} [AddCommGroup G] {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p)
    (H : AddSubgroup G) {y : G} (hy : y ∈ H) (hy0 : y ≠ 0) : H = ⊤ := by
  have : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact hp.ne_zero)
  have hd : Nat.card H ∣ p := hG ▸ AddSubgroup.card_addSubgroup_dvd_card H
  rcases (Nat.dvd_prime hp).1 hd with h | h
  · exact absurd (AddSubgroup.mem_bot.1 ((AddSubgroup.eq_bot_of_card_eq H h) ▸ hy)) hy0
  · exact AddSubgroup.eq_top_of_card_eq H (h.trans hG.symm)

/- English proof (translation)
Distinguish the cases in `h : ∀ y : G, e • y = 0`. Conclude with `Or.inl h`. Take `⟨y0, hy0⟩` from `not_forall.1 h right`. Establish `htop` using `subgroup_prime_card_eq_top hp hG (DistribSMul.toAddMonoidHom G e).range ⟨y0, rfl⟩ hy0`. Introduce `y`.

Establish `hy : y ∈ (DistribSMul.toAddMonoidHom G e).range` using `by rw [htop]; exact AddSubgroup.mem_top y`. Take `⟨z, hz⟩` from `AddMonoidHom.mem_range.1 hy`. Rewrite using `[← hz]`. Use `show e • e • z = e • z`. Rewrite using `[smul_smul, he]`.
-/
theorem idempotent_action_prime_card {O : Type} [Ring O] {G : Type} [AddCommGroup G] [Module O G] {p : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p) {e : O} (he : e * e = e) : (∀ y : G, e • y = 0) ∨ (∀ y : G, e • y = y) := by
  by_cases h : ∀ y : G, e • y = 0
  · exact Or.inl h
  · obtain ⟨y0, hy0⟩ := not_forall.1 h
    right
    have htop := subgroup_prime_card_eq_top hp hG (DistribSMul.toAddMonoidHom G e).range ⟨y0, rfl⟩ hy0
    intro y
    have hy : y ∈ (DistribSMul.toAddMonoidHom G e).range := by rw [htop]; exact AddSubgroup.mem_top y
    obtain ⟨z, hz⟩ := AddMonoidHom.mem_range.1 hy
    rw [← hz]
    show e • e • z = e • z
    rw [smul_smul, he]

/- English proof (translation)
Establish `hG : Nat.card K = p` using `by rw [Nat.card_eq_fintype_card, hK]`. Establish `htop` using `subgroup_prime_card_eq_top hp hG (AddSubgroup.zmultiples (1 : K)) (AddSubgroup.mem_zmultiples 1) one_ne_zero`. Establish `ha : (a : K) ∈ AddSubgroup.zmultiples (1 : K)` using `by rw [htop]; exact AddSubgroup.mem_top _`. Take `⟨k, hk⟩` from `AddSubgroup.mem_zmultiples_iff.1 ha`. Rewrite `hk` using `[zsmul_one]`.

Use `⟨k, hk, fun ⟨m, hm⟩ => a.ne_zero ?_⟩` and prove the remaining obligations. Establish `hp0 : (p : K) = 0`. Use `card_nsmul_eq_zero' (G := K) (x := 1)` as an intermediate fact. Rewrite `this` using `[hG, nsmul_eq_mul, mul_one]`. Then use the resulting hypothesis. Rewrite using `[← hk, hm, Int.cast_mul, Int.cast_natCast, hp0, zero_mul]`.
-/
theorem unit_lift_int_prime_field {K : Type} [Field K] [Fintype K] {p : ℕ} (hp : p.Prime) (hK : Fintype.card K = p) (a : Kˣ) :
    ∃ k : ℤ, (k : K) = a ∧ ¬ (p : ℤ) ∣ k := by
  have hG : Nat.card K = p := by rw [Nat.card_eq_fintype_card, hK]
  have htop := subgroup_prime_card_eq_top hp hG (AddSubgroup.zmultiples (1 : K)) (AddSubgroup.mem_zmultiples 1) one_ne_zero
  have ha : (a : K) ∈ AddSubgroup.zmultiples (1 : K) := by rw [htop]; exact AddSubgroup.mem_top _
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 ha
  rw [zsmul_one] at hk
  refine ⟨k, hk, fun ⟨m, hm⟩ => a.ne_zero ?_⟩
  have hp0 : (p : K) = 0 := by
    have := card_nsmul_eq_zero' (G := K) (x := 1)
    rwa [hG, nsmul_eq_mul, mul_one] at this
  rw [← hk, hm, Int.cast_mul, Int.cast_natCast, hp0, zero_mul]

end Prime

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Introduce `hkv`. Establish `h1 : ¬ T ∣ k.natAbs` using `fun h => hk (Int.natCast_dvd.2 h)`. Establish `h2 : Nat.Coprime T k.natAbs` using `(Nat.Prime.coprime_iff_not_dvd hT).2 h1`. Establish `hcop : IsCoprime k (T : ℤ)`. Rewrite using `[Int.isCoprime_iff_gcd_eq_one]`.

Conclude with `h2.symm`. Take `⟨a, b, hab⟩` from `hcop`. Establish `hmem : ((a * k + b * (T : ℤ) : ℤ) : 𝓞 F) ∈ v.asIdeal`. Use `push_cast`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ hkv) (Ideal.mul_mem_left _ _ hv)`.

Rewrite `hmem` using `[hab, Int.cast_one]`. Conclude with `v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hmem)`.
-/
theorem int_not_mem_prime_over (v : HeightOneSpectrum (𝓞 F)) {T : ℕ} (hT : T.Prime) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    {k : ℤ} (hk : ¬ (T : ℤ) ∣ k) : (k : 𝓞 F) ∉ v.asIdeal := by
  intro hkv
  have h1 : ¬ T ∣ k.natAbs := fun h => hk (Int.natCast_dvd.2 h)
  have h2 : Nat.Coprime T k.natAbs := (Nat.Prime.coprime_iff_not_dvd hT).2 h1
  have hcop : IsCoprime k (T : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact h2.symm
  obtain ⟨a, b, hab⟩ := hcop
  have hmem : ((a * k + b * (T : ℤ) : ℤ) : 𝓞 F) ∈ v.asIdeal := by
    push_cast
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hkv) (Ideal.mul_mem_left _ _ hv)
  rw [hab, Int.cast_one] at hmem
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hmem)

/- English proof (translation)
Establish `h` using `v.valuedAdicCompletion_eq_valuation (K := F) (k : 𝓞 F)`. Rewrite `h` using `[HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hk]`. Simplify using `using h`.
-/
theorem valuation_int_not_mem_eq_one (v : HeightOneSpectrum (𝓞 F)) {k : ℤ} (hk : (k : 𝓞 F) ∉ v.asIdeal) :
    Valued.v (k : v.adicCompletion F) = 1 := by
  have h := v.valuedAdicCompletion_eq_valuation (K := F) (k : 𝓞 F)
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hk] at h
  simpa using h

variable {n : ℕ} {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

/- English proof (translation)
Introduce `x`. Rewrite using `[hg]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `Λ.smul_mem (⟨μ, hμ⟩ : S) hx`.

Introduce `hx`. Establish `h` using `Λ.smul_mem (⟨μ', hμ'⟩ : S) hx`. Express the relevant statement in the definitionally equal form `μ' • μ • x ∈ Λ at h`. Rewrite `h` using `[smul_smul, h1, one_smul]`. Then use the resulting hypothesis.
-/
theorem scalar_mem_lattice_stabiliser {A : Type} [CommRing A] {S : Subring A} (Λ : Submodule S (Fin n → A))
    (g : GL (Fin n) A) (μ μ' : A) (hμ : μ ∈ S) (hμ' : μ' ∈ S) (h1 : μ' * μ = 1)
    (hg : ∀ x, (g : Matrix (Fin n) (Fin n) A) *ᵥ x = μ • x) : g ∈ stabGL Λ := by
  intro x
  rw [hg]
  constructor
  · intro hx
    exact Λ.smul_mem (⟨μ, hμ⟩ : S) hx
  · intro hx
    have h := Λ.smul_mem (⟨μ', hμ'⟩ : S) hx
    change μ' • μ • x ∈ Λ at h
    rwa [smul_smul, h1, one_smul] at h

/- English proof (translation)
Use `set μ : E ⊗[F] v.adicCompletion F := c * e + c' * (1 - e) with hμdef`. Use `set μ' : E ⊗[F] v.adicCompletion F := c * (1 - e) + c' * e with hμ'def`. Establish `hμμ' : μ * μ' = 1`. Rewrite using `[hμdef, hμ'def]`. Take the linear combination `(-c ^ 2 + 2 * c * c' - c' ^ 2) * hee + hcc`.

Establish `hμ'μ : μ' * μ = 1` using `by rw [mul_comm]; exact hμμ'`. Establish `hσμ : sigR σ (v.adicCompletion F) μ = μ'`. Rewrite using `[hμdef, hμ'def, map_add, map_mul, map_mul, map_sub, map_one, hσ, hσc, hσc']`. Expand and normalize the polynomial expressions, which then agree. Establish `hμO : μ ∈ intV E v` using `add_mem (mul_mem hc he) (mul_mem hc' (sub_mem (one_mem _) he))`.

Establish `hμ'O : μ' ∈ intV E v` using `add_mem (mul_mem hc (sub_mem (one_mem _) he)) (mul_mem hc' he)`. Set `M : GL (Fin n) (E ⊗[F] v.adicCompletion F)` to `⟨μ • (1 : Matrix (Fin n) (Fin n) _), μ' • (1 : Matrix (Fin n) (Fin n) _), by rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, hμμ', one_smul], by rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, hμ'μ, one_smul]⟩`. Establish `hmv : ∀ x : Fin n → E ⊗[F] v.adicCompletion F, (M : Matrix (Fin n) (Fin n) _) *ᵥ x = μ • x`. Introduce `x`. Use `show (μ • (1 : Matrix (Fin n) (Fin n) _)) *ᵥ x = μ • x`.

Rewrite using `[Matrix.smul_mulVec, Matrix.one_mulVec]`. Establish `hcT : cT (sigR σ (v.adicCompletion F)) (μ • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F))) = μ' • (1 : Matrix (Fin n) (Fin n) _)`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using `[cT, hσμ]`. Simplify using `[cT, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]`. Establish `hU : M ∈ UPts σ J (v.adicCompletion F)` using `by show cT (sigR σ (v.adicCompletion F)) (μ • (1 : Matrix (Fin n) (Fin n) _)) * J.map (inclE (F := F) (v.adicCompletion F)) * (μ • (1 : Matrix (Fin n) (Fin n) _)) = J.map (inclE (F := F) (v.adicCompletion F))`. Rewrite using `[hcT, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hμ'μ, one_smul]`. Establish `hL : M ∈ levelVL σ J v S.Lb` using `by show M ∈ UJ _ _ ⊓ stabGL _`.

Conclude with `Subgroup.mem_inf.2 ⟨hU, scalar_mem_lattice_stabiliser _ M μ μ' hμO hμ'O hμ'μ hmv⟩`. Establish `hg : M ∈ stabGL (latS (F` using `F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) := scalar_mem_lattice_stabiliser _ M μ μ' hμO hμ'O hμ'μ hmv`. Use `⟨M, hL, hg, fun x => ?_⟩` and prove the remaining obligations. Establish `hx : (⟨(M : Matrix (Fin n) (Fin n) _) *ᵥ x.1, (hg x.1).1 x.2⟩ : latS (F` using `F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) = (⟨μ, hμO⟩ : intV E v) • x := by`. Apply `Subtype.ext` to reduce the goal to its premises.

Conclude with `(hmv x.1).trans rfl`. Rewrite using `[hx, map_smul]`. Use `set y := S.fT v hv x`. Establish `hsplit : (⟨μ, hμO⟩ : intV E v) = ⟨c, hc⟩ * ⟨e, he⟩ + ⟨c', hc'⟩ * (1 - ⟨e, he⟩)` using `Subtype.ext rfl`. Establish `h1e : (1 - (⟨e, he⟩ : intV E v)) • y = 0` using `by rw [sub_smul, one_smul, hact y, sub_self]`.

Establish `hkO : ((k : intV E v)) * ⟨c, hc⟩ = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using hkc`. Rewrite using `[hsplit, add_smul, mul_smul, mul_smul, h1e, smul_zero, add_zero, hact y, ← Int.cast_smul_eq_zsmul (intV E v), smul_smul, hkO, one_smul]`.
-/
theorem local_diamond_of_idempotent (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : ℤ) (c c' e : E ⊗[F] v.adicCompletion F)
    (hc : c ∈ intV E v) (hc' : c' ∈ intV E v) (he : e ∈ intV E v) (hee : e * e = e)
    (hσ : sigR σ (v.adicCompletion F) e = 1 - e) (hσc : sigR σ (v.adicCompletion F) c = c)
    (hσc' : sigR σ (v.adicCompletion F) c' = c') (hcc : c * c' = 1)
    (hkc : (k : E ⊗[F] v.adicCompletion F) * c = 1)
    (hact : ∀ y : S.fM v hv, (⟨e, he⟩ : intV E v) • y = y) : IsLocalDiamond S v hv k := by
  set μ : E ⊗[F] v.adicCompletion F := c * e + c' * (1 - e) with hμdef
  set μ' : E ⊗[F] v.adicCompletion F := c * (1 - e) + c' * e with hμ'def
  have hμμ' : μ * μ' = 1 := by
    rw [hμdef, hμ'def]
    linear_combination (-c ^ 2 + 2 * c * c' - c' ^ 2) * hee + hcc
  have hμ'μ : μ' * μ = 1 := by rw [mul_comm]; exact hμμ'
  have hσμ : sigR σ (v.adicCompletion F) μ = μ' := by
    rw [hμdef, hμ'def, map_add, map_mul, map_mul, map_sub, map_one, hσ, hσc, hσc']
    ring
  have hμO : μ ∈ intV E v :=
    add_mem (mul_mem hc he) (mul_mem hc' (sub_mem (one_mem _) he))
  have hμ'O : μ' ∈ intV E v :=
    add_mem (mul_mem hc (sub_mem (one_mem _) he)) (mul_mem hc' he)
  let M : GL (Fin n) (E ⊗[F] v.adicCompletion F) :=
    ⟨μ • (1 : Matrix (Fin n) (Fin n) _), μ' • (1 : Matrix (Fin n) (Fin n) _),
      by rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, hμμ', one_smul],
      by rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, hμ'μ, one_smul]⟩
  have hmv : ∀ x : Fin n → E ⊗[F] v.adicCompletion F, (M : Matrix (Fin n) (Fin n) _) *ᵥ x = μ • x := by
    intro x
    show (μ • (1 : Matrix (Fin n) (Fin n) _)) *ᵥ x = μ • x
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  have hcT : cT (sigR σ (v.adicCompletion F)) (μ • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F))) =
      μ' • (1 : Matrix (Fin n) (Fin n) _) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [cT, hσμ]
    · simp [cT, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]
  have hU : M ∈ UPts σ J (v.adicCompletion F) := by
    show cT (sigR σ (v.adicCompletion F)) (μ • (1 : Matrix (Fin n) (Fin n) _)) *
        J.map (inclE (F := F) (v.adicCompletion F)) * (μ • (1 : Matrix (Fin n) (Fin n) _)) =
      J.map (inclE (F := F) (v.adicCompletion F))
    rw [hcT, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hμ'μ,
      one_smul]
  have hL : M ∈ levelVL σ J v S.Lb := by
    show M ∈ UJ _ _ ⊓ stabGL _
    exact Subgroup.mem_inf.2 ⟨hU, scalar_mem_lattice_stabiliser _ M μ μ' hμO hμ'O hμ'μ hmv⟩
  have hg : M ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) :=
    scalar_mem_lattice_stabiliser _ M μ μ' hμO hμ'O hμ'μ hmv
  refine ⟨M, hL, hg, fun x => ?_⟩
  have hx : (⟨(M : Matrix (Fin n) (Fin n) _) *ᵥ x.1, (hg x.1).1 x.2⟩ : latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) = (⟨μ, hμO⟩ : intV E v) • x := by
    apply Subtype.ext
    exact (hmv x.1).trans rfl
  rw [hx, map_smul]
  set y := S.fT v hv x
  have hsplit : (⟨μ, hμO⟩ : intV E v) = ⟨c, hc⟩ * ⟨e, he⟩ + ⟨c', hc'⟩ * (1 - ⟨e, he⟩) := Subtype.ext rfl
  have h1e : (1 - (⟨e, he⟩ : intV E v)) • y = 0 := by rw [sub_smul, one_smul, hact y, sub_self]
  have hkO : ((k : intV E v)) * ⟨c, hc⟩ = 1 := by
    apply Subtype.ext
    simpa using hkc
  rw [hsplit, add_smul, mul_smul, mul_smul, h1e, smul_zero, add_zero, hact y, ← Int.cast_smul_eq_zsmul (intV E v),
    smul_smul, hkO, one_smul]

/- English proof (translation)
Establish `hval` using `valuation_int_not_mem_eq_one v (int_not_mem_prime_over v hT hv hk)`. Establish `hk0 : (k : v.adicCompletion F) ≠ 0`. Introduce `h`. Rewrite `hval` using `[h, map_zero]`. Conclude with `zero_ne_one hval`.

Establish `hkI : (k : v.adicCompletion F) ∈ v.adicCompletionIntegers F`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, hval]`. Establish `hkI' : (k : v.adicCompletion F)⁻¹ ∈ v.adicCompletionIntegers F`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval, inv_one]`. Establish `hR : ∀ y ∈ v.adicCompletionIntegers F, ((1 : E) ⊗ₜ[F] y) ∈ intV E v` using `fun y hy => Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)`.

Establish `hσR : ∀ y : v.adicCompletion F, sigR σ (v.adicCompletion F) ((1 : E) ⊗ₜ[F] y) = (1 : E) ⊗ₜ[F] y`. Introduce `y`. Simplify using `[sigR]`. Establish `hcc : ((1 : E) ⊗ₜ[F] (k : v.adicCompletion F)⁻¹) * ((1 : E) ⊗ₜ[F] (k : v.adicCompletion F)) = 1`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hk0, Algebra.TensorProduct.one_def]`.

Establish `hkA : ((k : E ⊗[F] v.adicCompletion F)) = (1 : E) ⊗ₜ[F] (k : v.adicCompletion F)`. Rewrite using `[← Algebra.TensorProduct.includeRight_apply]`. Conclude with `(map_intCast _ k).symm`. Establish `hkc : ((k : E ⊗[F] v.adicCompletion F)) * ((1 : E) ⊗ₜ[F] (k : v.adicCompletion F)⁻¹) = 1`. Rewrite using `[hkA, mul_comm, hcc]`.

Break down `idempotent_action_prime_card hT (S.fM_card v hv) (e := (⟨e, he⟩ : intV E v)) (Subtype.ext hee) with h0 | h1` into its components or cases. Establish `he' : 1 - e ∈ intV E v` using `sub_mem (one_mem _) he`. Use `local_diamond_of_idempotent S v hv k _ _ (1 - e) (hR _ hkI') (hR _ hkI) he' (by linear_combination hee) (by rw [map_sub, map_one, hσ]) (hσR _) (hσR _) hcc hkc (fun y => ?_)` and prove the remaining obligations. Establish `: (⟨1 - e, he'⟩ : intV E v) = 1 - ⟨e, he⟩` using `Subtype.ext rfl`. Rewrite using `[this, sub_smul, one_smul, h0 y, sub_zero]`.

Conclude with `local_diamond_of_idempotent S v hv k _ _ e (hR _ hkI') (hR _ hkI) he hee hσ (hσR _) (hσR _) hcc hkc h1`.
-/
theorem local_diamond_of_split_idempotent (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) (hT : T.Prime) (k : ℤ) (hk : ¬ (T : ℤ) ∣ k) (e : E ⊗[F] v.adicCompletion F)
    (he : e ∈ intV E v) (hee : e * e = e) (hσ : sigR σ (v.adicCompletion F) e = 1 - e) : IsLocalDiamond S v hv k := by
  have hval := valuation_int_not_mem_eq_one v (int_not_mem_prime_over v hT hv hk)
  have hk0 : (k : v.adicCompletion F) ≠ 0 := by
    intro h; rw [h, map_zero] at hval; exact zero_ne_one hval
  have hkI : (k : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval]
  have hkI' : (k : v.adicCompletion F)⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval, inv_one]
  have hR : ∀ y ∈ v.adicCompletionIntegers F, ((1 : E) ⊗ₜ[F] y) ∈ intV E v := fun y hy =>
    Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  have hσR : ∀ y : v.adicCompletion F, sigR σ (v.adicCompletion F) ((1 : E) ⊗ₜ[F] y) = (1 : E) ⊗ₜ[F] y := by
    intro y; simp [sigR]
  have hcc : ((1 : E) ⊗ₜ[F] (k : v.adicCompletion F)⁻¹) * ((1 : E) ⊗ₜ[F] (k : v.adicCompletion F)) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hk0, Algebra.TensorProduct.one_def]
  have hkA : ((k : E ⊗[F] v.adicCompletion F)) = (1 : E) ⊗ₜ[F] (k : v.adicCompletion F) := by
    rw [← Algebra.TensorProduct.includeRight_apply]
    exact (map_intCast _ k).symm
  have hkc : ((k : E ⊗[F] v.adicCompletion F)) * ((1 : E) ⊗ₜ[F] (k : v.adicCompletion F)⁻¹) = 1 := by
    rw [hkA, mul_comm, hcc]
  rcases idempotent_action_prime_card hT (S.fM_card v hv) (e := (⟨e, he⟩ : intV E v)) (Subtype.ext hee) with h0 | h1
  · have he' : 1 - e ∈ intV E v := sub_mem (one_mem _) he
    refine local_diamond_of_idempotent S v hv k _ _ (1 - e) (hR _ hkI') (hR _ hkI) he' (by linear_combination hee)
      (by rw [map_sub, map_one, hσ]) (hσR _) (hσR _) hcc hkc (fun y => ?_)
    have : (⟨1 - e, he'⟩ : intV E v) = 1 - ⟨e, he⟩ := Subtype.ext rfl
    rw [this, sub_smul, one_smul, h0 y, sub_zero]
  · exact local_diamond_of_idempotent S v hv k _ _ e (hR _ hkI') (hR _ hkI) he hee hσ (hσR _) (hσR _) hcc hkc h1

end Local

section Tied

variable {D : D7} {u : D.what₂.Word}

def SplitAtT (A : AtTTied u) : Prop :=
  ∀ v : (D.mem u).A.vT, ∃ e ∈ intV D.host.E (A.eV v).1, e * e = e ∧
    sigR (sigD D) ((A.eV v).1.adicCompletion D.host.F) e = 1 - e

/- English proof (translation)
Introduce `i hi h0 v a`. Take `⟨k, hk, hkT⟩` from `unit_lift_int_prime_field (D.mem u).A.T_prime ((D.mem u).A.card_Fv v) a`. Take `⟨e, he, hee, hσ⟩` from `hs v`. Conclude with `⟨k, hk, local_diamond_of_split_idempotent (Tf.cls i hi h0).lev _ _ (D.mem u).A.T_prime k hkT e he hee hσ⟩`.
-/
theorem local_diamonds_of_split (Tf : Forms0 D u) (hs : SplitAtT Tf.atT) : LocalDiamondElementsExist Tf := by
  intro i hi h0 v a
  obtain ⟨k, hk, hkT⟩ := unit_lift_int_prime_field (D.mem u).A.T_prime ((D.mem u).A.card_Fv v) a
  obtain ⟨e, he, hee, hσ⟩ := hs v
  exact ⟨k, hk, local_diamond_of_split_idempotent (Tf.cls i hi h0).lev _ _ (D.mem u).A.T_prime k hkT e he hee hσ⟩

/- English proof (translation)
The claim follows from `diamond_elements_of_local Tf (local_diamonds_of_split Tf hs)`.
-/
theorem diamond_elements_of_split (Tf : Forms0 D u) (hs : SplitAtT Tf.atT) : DiamondElementsExist Tf :=
  diamond_elements_of_local Tf (local_diamonds_of_split Tf hs)

end Tied

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

end
