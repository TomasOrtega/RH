import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsAdapted
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramDetNeZeroOfIndep

open NumberField TensorProduct Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Adapted

section Field

variable {k V O : Type} [Field k] [AddCommGroup V] [Module k V] [CommRing O]

/- English proof (translation)
Establish `h` using `(Submodule.mem_iInf _).1 hx a`. Rewrite `h` using `[LinearMap.mem_ker]`. Simplify `h` using `[sub_eq_zero]`.
-/
theorem eigSp_apply {ρ : O →+* Module.End k V} {σ : O →+* k} {x : V} (hx : x ∈ eigSp ρ σ) (a : O) :
    ρ a x = σ a • x := by
  have h := (Submodule.mem_iInf _).1 hx a
  rw [LinearMap.mem_ker] at h
  simpa [sub_eq_zero] using h

/- English proof (translation)
Establish `hle : (⨆ τ ∈ T, eigSp ρ τ) ≤ (⨆ τ ∈ T, eigSp ρ τ).comap (ρ a)`. Use `iSup₂_le fun τ hτ y hy => ?_` and prove the remaining obligations. Rewrite using `[Submodule.mem_comap, eigSp_apply hy a]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem τ (Submodule.mem_iSup_of_mem hτ hy))`. Conclude with `hle hx`.
-/
theorem iSup_eigSp_stable (ρ : O →+* Module.End k V) (T : Set (O →+* k)) (a : O) {x : V}
    (hx : x ∈ ⨆ τ ∈ T, eigSp ρ τ) : ρ a x ∈ ⨆ τ ∈ T, eigSp ρ τ := by
  have hle : (⨆ τ ∈ T, eigSp ρ τ) ≤ (⨆ τ ∈ T, eigSp ρ τ).comap (ρ a) := by
    refine iSup₂_le fun τ hτ y hy => ?_
    rw [Submodule.mem_comap, eigSp_apply hy a]
    exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem τ (Submodule.mem_iSup_of_mem hτ hy))
  exact hle hx

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty`. Introduce `x _ h`. Simplify using `using h`. Consider the case `insert τ t _ ih`.

Introduce `x hx hxs`. Rewrite `hxs` using `[Finset.iSup_insert, Submodule.mem_sup]`. Take `⟨y, hy, z, hz, hyz⟩` from `hxs`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, σ a ≠ τ.1 a := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `τ.2 (RingHom.ext fun a => (h a).symm)`. Establish `hzs : ∀ b : O, ρ b z ∈ ⨆ i ∈ t, eigSp ρ i.1`. Introduce `b`. Establish `hle : (⨆ i ∈ t, eigSp ρ i.1) ≤ (⨆ i ∈ t, eigSp ρ i.1).comap (ρ b)`.

Use `iSup₂_le fun i hi u hu => ?_` and prove the remaining obligations. Rewrite using `[Submodule.mem_comap, eigSp_apply hu b]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi hu))`. Conclude with `hle hz`. Establish `hkey : (σ a - τ.1 a) • x = ρ a z - τ.1 a • z`.

Establish `e1` using `eigSp_apply hx a`. Establish `e2` using `eigSp_apply hy a`. Rewrite `e1` using `[← hyz, map_add, e2]`. Establish `e3 : ρ a z = σ a • (y + z) - τ.1 a • y` using `by rw [← e1]; abel`. Rewrite using `[e3, ← hyz, sub_smul]`.

Simplify using `only [smul_add]`. Normalize the expressions using the abelian group laws. Establish `hmem : (σ a - τ.1 a) • x ∈ ⨆ i ∈ t, eigSp ρ i.1`. Rewrite using `[hkey]`. Conclude with `Submodule.sub_mem _ (hzs a) (Submodule.smul_mem _ _ hz)`.

Establish `h0` using `ih _ (Submodule.smul_mem _ _ hx) hmem`. Conclude with `(smul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 ha)`.
-/
theorem eq_zero_of_mem_finset (ρ : O →+* Module.End k V) (σ : O →+* k)
    (t : Finset {τ : O →+* k // τ ≠ σ}) :
    ∀ x ∈ eigSp ρ σ, x ∈ (⨆ i ∈ t, eigSp ρ i.1) → x = 0 := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro x _ h
    simpa using h
  | insert τ t _ ih =>
    intro x hx hxs
    rw [Finset.iSup_insert, Submodule.mem_sup] at hxs
    obtain ⟨y, hy, z, hz, hyz⟩ := hxs
    obtain ⟨a, ha⟩ : ∃ a, σ a ≠ τ.1 a := by
      by_contra h
      push_neg at h
      exact τ.2 (RingHom.ext fun a => (h a).symm)
    have hzs : ∀ b : O, ρ b z ∈ ⨆ i ∈ t, eigSp ρ i.1 := by
      intro b
      have hle : (⨆ i ∈ t, eigSp ρ i.1) ≤ (⨆ i ∈ t, eigSp ρ i.1).comap (ρ b) := by
        refine iSup₂_le fun i hi u hu => ?_
        rw [Submodule.mem_comap, eigSp_apply hu b]
        exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi hu))
      exact hle hz
    have hkey : (σ a - τ.1 a) • x = ρ a z - τ.1 a • z := by
      have e1 := eigSp_apply hx a
      have e2 := eigSp_apply hy a
      rw [← hyz, map_add, e2] at e1
      have e3 : ρ a z = σ a • (y + z) - τ.1 a • y := by rw [← e1]; abel
      rw [e3, ← hyz, sub_smul]
      simp only [smul_add]
      abel
    have hmem : (σ a - τ.1 a) • x ∈ ⨆ i ∈ t, eigSp ρ i.1 := by
      rw [hkey]
      exact Submodule.sub_mem _ (hzs a) (Submodule.smul_mem _ _ hz)
    have h0 := ih _ (Submodule.smul_mem _ _ hx) hmem
    exact (smul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 ha)

/- English proof (translation)
Establish `h : (⨆ τ ∈ {τ : O →+* k | τ ≠ σ}, eigSp ρ τ) = ⨆ i : {τ : O →+* k // τ ≠ σ}, eigSp ρ i.1`. Rewrite using `[iSup_subtype']`. Both sides reduce to the same expression. Rewrite `hS` using `[h, Submodule.mem_iSup_iff_exists_finset]`. Take `⟨t, ht⟩` from `hS`.

Conclude with `eq_zero_of_mem_finset ρ σ t x hx ht`.
-/
theorem eq_zero_of_mem_iSup (ρ : O →+* Module.End k V) (σ : O →+* k) {x : V} (hx : x ∈ eigSp ρ σ)
    (hS : x ∈ ⨆ τ ∈ {τ : O →+* k | τ ≠ σ}, eigSp ρ τ) : x = 0 := by
  have h : (⨆ τ ∈ {τ : O →+* k | τ ≠ σ}, eigSp ρ τ) = ⨆ i : {τ : O →+* k // τ ≠ σ}, eigSp ρ i.1 := by
    rw [iSup_subtype']
    rfl
  rw [h, Submodule.mem_iSup_iff_exists_finset] at hS
  obtain ⟨t, ht⟩ := hS
  exact eq_zero_of_mem_finset ρ σ t x hx ht

/- English proof (translation)
Distinguish the cases in `h : ∃ p ∈ eigSp ρ σ, x - p ∈ ⨆ σ' ∈ {σ' : O →+* k | σ' ≠ σ}, eigSp ρ σ'`. Establish `e : eigComp ρ σ x = h.choose`. Unfold `eigComp`. Rewrite using `[dif_pos h]`. Rewrite using `[e]`.

Conclude with `h.choose_spec`. Conclude with `absurd (by unfold eigComp; rw [dif_neg h]) h0`.
-/
theorem eigComp_spec {ρ : O →+* Module.End k V} {σ : O →+* k} {x : V} (h0 : eigComp ρ σ x ≠ 0) :
    eigComp ρ σ x ∈ eigSp ρ σ ∧ x - eigComp ρ σ x ∈ ⨆ τ ∈ {τ : O →+* k | τ ≠ σ}, eigSp ρ τ := by
  by_cases h : ∃ p ∈ eigSp ρ σ, x - p ∈ ⨆ σ' ∈ {σ' : O →+* k | σ' ≠ σ}, eigSp ρ σ'
  · have e : eigComp ρ σ x = h.choose := by
      unfold eigComp
      rw [dif_pos h]
    rw [e]
    exact h.choose_spec
  · exact absurd (by unfold eigComp; rw [dif_neg h]) h0

end Field

section Main

variable {E L Ψ : Type} [Field E] [NumberField E] [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module L V]
  [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V]

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg c`. Use `set S : Submodule L V := ⨆ τ ∈ {τ : 𝓞 E →+* L | τ ≠ A.σ s}, eigSp A.ρ τ with hSdef`. Use `set p : Fin r → V := fun i => eigComp A.ρ (A.σ s) (v i) with hpdef`. Establish `hfam_l : ∀ i : Fin r, A.fam s v q (Fin.castAdd k i) = p i`.

Introduce `i`. Simplify using `[LinPt.fam, hpdef]`. Establish `hfam_r : ∀ c : Fin k, A.fam s v q (Fin.natAdd r c) = (q c : V)`. Introduce `c`. Simplify using `[LinPt.fam]`.

Establish `hp : ∀ i, p i ∈ eigSp A.ρ (A.σ s) ∧ v i - p i ∈ S`. Introduce `i`. Use `eigComp_spec ?_` and prove the remaining obligations. Use `hA.1.ne_zero (Fin.castAdd k i)` as an intermediate fact. Rewrite `this` using `[hfam_l]`. Then use the resulting hypothesis.

Use `set M : Submodule L V := Submodule.span L (Set.range p) ⊔ S with hMdef`. Establish `hT : ∀ (a : 𝓞 E) (i : Fin r), A.ρ a (v i) ∈ M`. Introduce `a i`. Establish `e : A.ρ a (v i) = A.σ s a • p i + A.ρ a (v i - p i)`. Rewrite using `[map_sub, eigSp_apply (hp i).1 a]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations. Conclude with `Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))`. Conclude with `Submodule.mem_sup_right (iSup_eigSp_stable A.ρ _ a (hp i).2)`.

Establish `hoS : oSpan A.ρ v ≤ M.toAddSubgroup`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `x ⟨a, i, rfl⟩`. Conclude with `hT a i`. Establish `hI : ∀ x ∈ A.I, x ∈ M`.

Introduce `x hx`. Take `⟨n, hn, -, hnx⟩` from `AddSubgroup.exists_nsmul_mem_of_relIndex_ne_zero hO.2.2 hx`. Establish `h1 : n • x ∈ M` using `hoS hnx.1`. Establish `hn0 : (n : L) ≠ 0` using `Nat.cast_ne_zero.2 hn.ne'`. Establish `h2 : x = (n : L)⁻¹ • (n • x)`.

Rewrite using `[← Nat.cast_smul_eq_nsmul L, smul_smul, inv_mul_cancel₀ hn0, one_smul]`. Rewrite using `[h2]`. Conclude with `Submodule.smul_mem _ _ h1`. Use `set w : A.Λ := ∑ c, g c • q c with hw`. Establish `hwV : (w : V) = ∑ c, g c • (q c : V)`.

Simplify using `[hw]`. Establish `hfw : A.f w = 0`. Simplify `hg` using `[hw, map_sum]`. Establish `hwI : (w : V) ∈ Submodule.span (𝓞 L) (A.I : Set V)` using `(A.ker w).1 hfw`. Establish `hwe : (w : V) ∈ eigSp A.ρ (A.σ s)`.

Establish `: (w : V) ∈ (eigSp A.ρ (A.σ s)).restrictScalars (𝓞 L)`. Rewrite using `[hwV]`. Conclude with `Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hq c).2`. Conclude with `this`. Establish `hwM : (w : V) ∈ M`.

Establish `hle : Submodule.span (𝓞 L) (A.I : Set V) ≤ M.restrictScalars (𝓞 L)` using `Submodule.span_le.2 fun x hx => hI x hx`. Conclude with `hle hwI`. Take `⟨u, hu, t, ht, hut⟩` from `Submodule.mem_sup.1 hwM`. Establish `hue : u ∈ eigSp A.ρ (A.σ s)`. Use `(Submodule.span_le.2 ?_) hu` and prove the remaining obligations.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `(hp i).1`. Establish `ht0 : t = 0`. Use `eq_zero_of_mem_iSup A.ρ (A.σ s) ?_ ht` and prove the remaining obligations. Establish `: t = (w : V) - u` using `by rw [← hut]; abel`.

Rewrite using `[this]`. Conclude with `Submodule.sub_mem _ hwe hue`. Take `⟨b, hb⟩` from `(Submodule.mem_span_range_iff_exists_fun L).1 hu`. Establish `hzero : ∑ j, (Fin.append (fun i => - b i) (fun c => algebraMap (𝓞 L) L (g c)) j) • A.fam s v q j = 0`. Rewrite using `[Fin.sum_univ_add]`.

Simplify using `only [Fin.append_left, Fin.append_right, hfam_l, hfam_r, neg_smul, algebraMap_smul, Finset.sum_neg_distrib]`. Rewrite using `[hb, ← hwV, ← hut, ht0]`. Simplify using the standard rewrite rules. Use `Fintype.linearIndependent_iff.1 hA.1 _ hzero (Fin.natAdd r c)` as an intermediate fact. Rewrite `this` using `[Fin.append_right]`.

Conclude with `RingOfIntegers.coe_injective (by simpa using this)`.
-/
theorem linearIndependent_f (A : LinPt E L Ψ V) (s : Ψ ⊕ Ψ) {r k : ℕ} (v : Fin r → V) (q : Fin k → A.Λ)
    (hO : IsOFamily A.ρ A.I v) (hA : A.IsAdapted s v q) (hq : ∀ i, (q i : V) ∈ A.eig s) :
    LinearIndependent (𝓞 L) fun c => A.f (q c) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg c
  set S : Submodule L V := ⨆ τ ∈ {τ : 𝓞 E →+* L | τ ≠ A.σ s}, eigSp A.ρ τ with hSdef
  set p : Fin r → V := fun i => eigComp A.ρ (A.σ s) (v i) with hpdef
  have hfam_l : ∀ i : Fin r, A.fam s v q (Fin.castAdd k i) = p i := by
    intro i
    simp [LinPt.fam, hpdef]
  have hfam_r : ∀ c : Fin k, A.fam s v q (Fin.natAdd r c) = (q c : V) := by
    intro c
    simp [LinPt.fam]
  have hp : ∀ i, p i ∈ eigSp A.ρ (A.σ s) ∧ v i - p i ∈ S := by
    intro i
    refine eigComp_spec ?_
    have := hA.1.ne_zero (Fin.castAdd k i)
    rwa [hfam_l] at this
  set M : Submodule L V := Submodule.span L (Set.range p) ⊔ S with hMdef
  have hT : ∀ (a : 𝓞 E) (i : Fin r), A.ρ a (v i) ∈ M := by
    intro a i
    have e : A.ρ a (v i) = A.σ s a • p i + A.ρ a (v i - p i) := by
      rw [map_sub, eigSp_apply (hp i).1 a]
      abel
    rw [e]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.mem_sup_left
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    · exact Submodule.mem_sup_right (iSup_eigSp_stable A.ρ _ a (hp i).2)
  have hoS : oSpan A.ρ v ≤ M.toAddSubgroup := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro x ⟨a, i, rfl⟩
    exact hT a i
  have hI : ∀ x ∈ A.I, x ∈ M := by
    intro x hx
    obtain ⟨n, hn, -, hnx⟩ := AddSubgroup.exists_nsmul_mem_of_relIndex_ne_zero hO.2.2 hx
    have h1 : n • x ∈ M := hoS hnx.1
    have hn0 : (n : L) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have h2 : x = (n : L)⁻¹ • (n • x) := by
      rw [← Nat.cast_smul_eq_nsmul L, smul_smul, inv_mul_cancel₀ hn0, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ h1
  set w : A.Λ := ∑ c, g c • q c with hw
  have hwV : (w : V) = ∑ c, g c • (q c : V) := by
    simp [hw]
  have hfw : A.f w = 0 := by
    simpa [hw, map_sum] using hg
  have hwI : (w : V) ∈ Submodule.span (𝓞 L) (A.I : Set V) := (A.ker w).1 hfw
  have hwe : (w : V) ∈ eigSp A.ρ (A.σ s) := by
    have : (w : V) ∈ (eigSp A.ρ (A.σ s)).restrictScalars (𝓞 L) := by
      rw [hwV]
      exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hq c).2
    exact this
  have hwM : (w : V) ∈ M := by
    have hle : Submodule.span (𝓞 L) (A.I : Set V) ≤ M.restrictScalars (𝓞 L) :=
      Submodule.span_le.2 fun x hx => hI x hx
    exact hle hwI
  obtain ⟨u, hu, t, ht, hut⟩ := Submodule.mem_sup.1 hwM
  have hue : u ∈ eigSp A.ρ (A.σ s) := by
    refine (Submodule.span_le.2 ?_) hu
    rintro _ ⟨i, rfl⟩
    exact (hp i).1
  have ht0 : t = 0 := by
    refine eq_zero_of_mem_iSup A.ρ (A.σ s) ?_ ht
    have : t = (w : V) - u := by rw [← hut]; abel
    rw [this]
    exact Submodule.sub_mem _ hwe hue
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun L).1 hu
  have hzero : ∑ j, (Fin.append (fun i => - b i) (fun c => algebraMap (𝓞 L) L (g c)) j) • A.fam s v q j = 0 := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, hfam_l, hfam_r, neg_smul, algebraMap_smul,
      Finset.sum_neg_distrib]
    rw [hb, ← hwV, ← hut, ht0]
    simp
  have := Fintype.linearIndependent_iff.1 hA.1 _ hzero (Fin.natAdd r c)
  rw [Fin.append_right] at this
  exact RingOfIntegers.coe_injective (by simpa using this)

end Main

end GlobalTheory.CompanionTheory.Ar.Cusp.Adapted

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open scoped ComplexOrder in

/- English proof (translation)
Introduce `E L Ψ _ _ _ _ V _ _ _ _ A s r k v q hO hA hq e`. Establish `hli` using `Adapted.linearIndependent_f A s v q hO hA hq`. Establish `hG : (Matrix.gram ℂ fun i ↦ fibreVec A.Bq.metric e (A.f (q i))) = Matrix.of fun i j ↦ (A.Bq.metric.form e).inner ((1 : ComplexAt e) ⊗ₜ[𝓞 L] A.f (q i)) ((1 : ComplexAt e) ⊗ₜ[𝓞 L] A.f (q j))`. Use extensionality with `i j`. Both sides reduce to the same expression.

Establish `hp` using `(Matrix.posDef_gram_of_linearIndependent (linearIndependent_fibreVec A.Bq.metric e hli)).det_pos`. Rewrite `hp` using `[hG]`. Conclude with `(Complex.lt_def.1 hp).1`.
-/
theorem gramDet_pos_of_adapted : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] (V : Type)
    [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (s : Ψ ⊕ Ψ) (r k : ℕ)
    (v : Fin r → V) (q : Fin k → A.Λ), IsOFamily A.ρ A.I v → A.IsAdapted s v q → (∀ i, (q i : V) ∈ A.eig s) →
    ∀ e : L →+* ℂ, 0 < A.gramDet e q := by
  intro E L Ψ _ _ _ _ V _ _ _ _ A s r k v q hO hA hq e
  have hli := Adapted.linearIndependent_f A s v q hO hA hq
  have hG : (Matrix.gram ℂ fun i ↦ fibreVec A.Bq.metric e (A.f (q i))) =
      Matrix.of fun i j ↦ (A.Bq.metric.form e).inner
        ((1 : ComplexAt e) ⊗ₜ[𝓞 L] A.f (q i)) ((1 : ComplexAt e) ⊗ₜ[𝓞 L] A.f (q j)) := by
    ext i j
    rfl
  have hp := (Matrix.posDef_gram_of_linearIndependent (linearIndependent_fibreVec A.Bq.metric e hli)).det_pos
  rw [hG] at hp
  exact (Complex.lt_def.1 hp).1

end GlobalTheory.CompanionTheory.Ar.Cusp
