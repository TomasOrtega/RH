import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA.Box

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Set `R` to `fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F`. Set `A` to `fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))`. Establish `hAo : ∀ v, IsOpen (A v)` using `fun v => Valued.isOpen_valuationSubring _`. Establish `hx : Set.Finite {v | x v ∉ A v}` using `x.2`. Set `S0 : Finset (HeightOneSpectrum (𝓞 F))` to `hx.toFinset`.

Establish `hS0 : ∀ v, v ∉ S0 → x v ∈ A v`. Introduce `v hv`. Assume the negation of the conclusion as `h`. Conclude with `hv (by simpa [S0] using h)`. Establish `hS : Filter.cofinite ≤ Filter.principal ((S0 : Set (HeightOneSpectrum (𝓞 F)))ᶜ)`.

Rewrite using `[Filter.le_principal_iff, Filter.mem_cofinite, compl_compl]`. Conclude with `S0.finite_toSet`. Establish `hemb` using `RestrictedProduct.isOpenEmbedding_inclusion_principal (R := R) hAo hS`. Establish `hr : ∀ y : Af F, (∀ v, v ∉ S0 → y v ∈ A v) → y ∈ Set.range (RestrictedProduct.inclusion R A hS)`. Introduce `y hy`.

Rewrite using `[RestrictedProduct.range_inclusion]`. Conclude with `Filter.eventually_principal.2 fun v hv => hy v hv`. Take `⟨x', hx'⟩` from `hr x hS0`. Establish `hW' : RestrictedProduct.inclusion R A hS ⁻¹' W ∈ 𝓝 x'` using `hemb.continuous.continuousAt.preimage_mem_nhds (by rw [hx']; exact hW)`. Rewrite `hW'` using `[(RestrictedProduct.isEmbedding_coe_of_principal (R := R) (A := A) (S := (S0 : Set (HeightOneSpectrum (𝓞 F)))ᶜ)).isInducing.nhds_eq_comap, Filter.mem_comap]`.

Take `⟨t, ht, htW⟩` from `hW'`. Rewrite `ht` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, hI, u, hu, hIu⟩` from `ht`. Establish `hval : ∀ v, x' v = x v` using `fun v => by rw [← hx']; rfl`. Use `⟨S0 ∪ hI.toFinset, fun v => u v ∩ (if v ∈ S0 then Set.univ else A v), ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `v`. Use `Filter.inter_mem (by rw [← hval]; exact hu v) ?_` and prove the remaining obligations. Distinguish the cases in `h : v ∈ S0`. Simplify using `[h]`. Simplify `(hAo v).mem_nhds (hS0 v h)` using `[h]`.

Introduce `v hv z hz`. Establish `h : v ∉ S0` using `fun h => hv (Finset.mem_union_left _ h)`. Establish `h2` using `hz.2`. Rewrite `h2` using `[if_neg h]`. Conclude with `h2`.

Introduce `y hy1 hy2`. Establish `hyA : ∀ v, v ∉ S0 → y v ∈ A v`. Introduce `v hv`. Distinguish the cases in `h : v ∈ S0 ∪ hI.toFinset`. Simplify `(hy1 v h).2` using `[hv]`.

Conclude with `hy2 v h`. Take `⟨y', hy'⟩` from `hr y hyA`. Establish `hval' : ∀ v, y' v = y v` using `fun v => by rw [← hy']; rfl`. Establish `: y' ∈ RestrictedProduct.inclusion R A hS ⁻¹' W`. Use `htW (hIu fun v hv => ?_)` and prove the remaining obligations.

Establish `hv' : v ∈ S0 ∪ hI.toFinset` using `Finset.mem_union_right _ (by simpa using hv)`. Use `show y' v ∈ u v`. Rewrite using `[hval']`. Conclude with `(hy1 v hv').1`. Establish `hz : RestrictedProduct.inclusion R A hS y' ∈ W` using `this`.

Rewrite `hz` using `[hy']`. Conclude with `hz`.
-/
theorem af_box (x : Af F) (W : Set (Af F)) (hW : W ∈ 𝓝 x) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ U : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F),
      (∀ v, U v ∈ 𝓝 (x v)) ∧
      (∀ v, v ∉ S → U v ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) ∧
      ∀ y : Af F, (∀ v ∈ S, y v ∈ U v) →
        (∀ v, v ∉ S → y v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) → y ∈ W := by
  classical
  let R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hAo : ∀ v, IsOpen (A v) := fun v => Valued.isOpen_valuationSubring _
  have hx : Set.Finite {v | x v ∉ A v} := x.2
  let S0 : Finset (HeightOneSpectrum (𝓞 F)) := hx.toFinset
  have hS0 : ∀ v, v ∉ S0 → x v ∈ A v := by
    intro v hv
    by_contra h
    exact hv (by simpa [S0] using h)
  have hS : Filter.cofinite ≤ Filter.principal ((S0 : Set (HeightOneSpectrum (𝓞 F)))ᶜ) := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite, compl_compl]
    exact S0.finite_toSet
  have hemb := RestrictedProduct.isOpenEmbedding_inclusion_principal (R := R) hAo hS
  have hr : ∀ y : Af F, (∀ v, v ∉ S0 → y v ∈ A v) →
      y ∈ Set.range (RestrictedProduct.inclusion R A hS) := by
    intro y hy
    rw [RestrictedProduct.range_inclusion]
    exact Filter.eventually_principal.2 fun v hv => hy v hv
  obtain ⟨x', hx'⟩ := hr x hS0
  have hW' : RestrictedProduct.inclusion R A hS ⁻¹' W ∈ 𝓝 x' :=
    hemb.continuous.continuousAt.preimage_mem_nhds (by rw [hx']; exact hW)
  rw [(RestrictedProduct.isEmbedding_coe_of_principal (R := R) (A := A)
    (S := (S0 : Set (HeightOneSpectrum (𝓞 F)))ᶜ)).isInducing.nhds_eq_comap, Filter.mem_comap] at hW'
  obtain ⟨t, ht, htW⟩ := hW'
  rw [nhds_pi, Filter.mem_pi] at ht
  obtain ⟨I, hI, u, hu, hIu⟩ := ht
  have hval : ∀ v, x' v = x v := fun v => by rw [← hx']; rfl
  refine ⟨S0 ∪ hI.toFinset, fun v => u v ∩ (if v ∈ S0 then Set.univ else A v), ?_, ?_, ?_⟩
  · intro v
    refine Filter.inter_mem (by rw [← hval]; exact hu v) ?_
    by_cases h : v ∈ S0
    · simp [h]
    · simpa [h] using (hAo v).mem_nhds (hS0 v h)
  · intro v hv z hz
    have h : v ∉ S0 := fun h => hv (Finset.mem_union_left _ h)
    have h2 := hz.2
    rw [if_neg h] at h2
    exact h2
  · intro y hy1 hy2
    have hyA : ∀ v, v ∉ S0 → y v ∈ A v := by
      intro v hv
      by_cases h : v ∈ S0 ∪ hI.toFinset
      · simpa [hv] using (hy1 v h).2
      · exact hy2 v h
    obtain ⟨y', hy'⟩ := hr y hyA
    have hval' : ∀ v, y' v = y v := fun v => by rw [← hy']; rfl
    have : y' ∈ RestrictedProduct.inclusion R A hS ⁻¹' W := by
      refine htW (hIu fun v hv => ?_)
      have hv' : v ∈ S0 ∪ hI.toFinset := Finset.mem_union_right _ (by simpa using hv)
      show y' v ∈ u v
      rw [hval']
      exact (hy1 v hv').1
    have hz : RestrictedProduct.inclusion R A hS y' ∈ W := this
    rw [hy'] at hz
    exact hz

/- English proof (translation)
Rewrite `hA` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, -, t, ht, hIt⟩` from `hA`. Conclude with `⟨t, ht, fun y hy => hIt fun i _ => hy i⟩`.
-/
theorem pi_box {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] (x : ∀ i, X i)
    (A : Set (∀ i, X i)) (hA : A ∈ 𝓝 x) :
    ∃ t : ∀ i, Set (X i), (∀ i, t i ∈ 𝓝 (x i)) ∧ ∀ y : ∀ i, X i, (∀ i, y i ∈ t i) → y ∈ A := by
  rw [nhds_pi, Filter.mem_pi] at hA
  obtain ⟨I, -, t, ht, hIt⟩ := hA
  exact ⟨t, ht, fun y hy => hIt fun i _ => hy i⟩

/- English proof (translation)
Establish `hW' : W ∈ 𝓝 ((x.1, x.2) : Ainf F × Af F)` using `hW`. Take `⟨A, hA, B, hB, hAB⟩` from `mem_nhds_prod_iff.1 hW'`. Take `⟨t, ht, hIt⟩` from `pi_box (X := fun w : InfinitePlace F => w.Completion) x.1 A hA`. Take `⟨S, V, hV, hVO, hSV⟩` from `af_box x.2 B hB`. Use `⟨Finset.univ.map Function.Embedding.inl ∪ S.map Function.Embedding.inr, fun u => match u with` and prove the remaining obligations.

Consider the case `.inl w => t w`. Consider the case `.inr v => V v, ?_, ?_, ?_, ?_⟩`. Introduce and unpack `(w | v)`. Conclude with `ht w`. Conclude with `hV v`.

Introduce `w`. Conclude with `Finset.mem_union_left _ (Finset.mem_map.2 ⟨w, Finset.mem_univ _, rfl⟩)`. Introduce `v hv`. Conclude with `hVO v fun h => hv (Finset.mem_union_right _ (Finset.mem_map.2 ⟨v, h, rfl⟩))`. Introduce `y hy1 hy2`.

Establish `h1 : y.1 ∈ A` using `hIt y.1 fun w => hy1 (Sum.inl w) (Finset.mem_union_left _ (Finset.mem_map.2 ⟨w, Finset.mem_univ _, rfl⟩))`. Establish `h2 : y.2 ∈ B`. Use `hSV y.2 (fun v hv => ?_) (fun v hv => ?_)` and prove the remaining obligations. Conclude with `hy1 (Sum.inr v) (Finset.mem_union_right _ (Finset.mem_map.2 ⟨v, hv, rfl⟩))`. Distinguish the cases in `h : (Sum.inr v : Pl F) ∈ Finset.univ.map Function.Embedding.inl ∪ S.map Function.Embedding.inr`.

Break down `Finset.mem_union.1 h with h | h` into its components or cases. Take `⟨w, -, hw⟩` from `Finset.mem_map.1 h`. Consider the cases of `hw`. Take `⟨v', hv', e⟩` from `Finset.mem_map.1 h`. Consider the cases of `e`.

Conclude with `absurd hv' hv`. Conclude with `hy2 v h`. Conclude with `hAB (Set.mk_mem_prod h1 h2)`.
-/
theorem adele_box (x : AF F) (W : Set (AF F)) (hW : W ∈ 𝓝 x) :
    ∃ T : Finset (Pl F), ∃ U : (u : Pl F) → Set (Kp u),
      (∀ u, U u ∈ 𝓝 (proj u x)) ∧ (∀ w : InfinitePlace F, (Sum.inl w : Pl F) ∈ T) ∧
      (∀ v : HeightOneSpectrum (𝓞 F), (Sum.inr v : Pl F) ∉ T → U (Sum.inr v) ⊆ Ov v) ∧
      ∀ y : AF F, (∀ u ∈ T, proj u y ∈ U u) →
        (∀ v : HeightOneSpectrum (𝓞 F), (Sum.inr v : Pl F) ∉ T → proj (Sum.inr v) y ∈ Ov v) → y ∈ W := by
  classical
  have hW' : W ∈ 𝓝 ((x.1, x.2) : Ainf F × Af F) := hW
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 hW'
  obtain ⟨t, ht, hIt⟩ := pi_box (X := fun w : InfinitePlace F => w.Completion) x.1 A hA
  obtain ⟨S, V, hV, hVO, hSV⟩ := af_box x.2 B hB
  refine ⟨Finset.univ.map Function.Embedding.inl ∪ S.map Function.Embedding.inr,
    fun u => match u with
      | .inl w => t w
      | .inr v => V v, ?_, ?_, ?_, ?_⟩
  · rintro (w | v)
    · exact ht w
    · exact hV v
  · intro w
    exact Finset.mem_union_left _ (Finset.mem_map.2 ⟨w, Finset.mem_univ _, rfl⟩)
  · intro v hv
    exact hVO v fun h => hv (Finset.mem_union_right _ (Finset.mem_map.2 ⟨v, h, rfl⟩))
  · intro y hy1 hy2
    have h1 : y.1 ∈ A := hIt y.1 fun w =>
      hy1 (Sum.inl w) (Finset.mem_union_left _ (Finset.mem_map.2 ⟨w, Finset.mem_univ _, rfl⟩))
    have h2 : y.2 ∈ B := by
      refine hSV y.2 (fun v hv => ?_) (fun v hv => ?_)
      · exact hy1 (Sum.inr v) (Finset.mem_union_right _ (Finset.mem_map.2 ⟨v, hv, rfl⟩))
      · by_cases h : (Sum.inr v : Pl F) ∈ Finset.univ.map Function.Embedding.inl ∪
            S.map Function.Embedding.inr
        · rcases Finset.mem_union.1 h with h | h
          · obtain ⟨w, -, hw⟩ := Finset.mem_map.1 h
            cases hw
          · obtain ⟨v', hv', e⟩ := Finset.mem_map.1 h
            cases e
            exact absurd hv' hv
        · exact hy2 v h
    exact hAB (Set.mk_mem_prod h1 h2)

/- English proof (translation)
Introduce `V hV`. Set `e` to `qHomeo (d := d) (β := β) (R := AF F)`. Establish `h0 : e.symm ⁻¹' V ∈ 𝓝 (a.re, a.imI, a.imJ, a.imK)`. Use `e.symm.continuous.continuousAt.preimage_mem_nhds ?_` and prove the remaining obligations. Establish `: e.symm (a.re, a.imI, a.imJ, a.imK) = a` using `e.symm_apply_apply a`.

Rewrite using `[this]`. Conclude with `hV`. Take `⟨W1, h1, R1, hR1, hs1⟩` from `mem_nhds_prod_iff.1 h0`. Take `⟨W2, h2, R2, hR2, hs2⟩` from `mem_nhds_prod_iff.1 hR1`. Take `⟨W3, h3, W4, h4, hs3⟩` from `mem_nhds_prod_iff.1 hR2`.

Take `⟨T1, U1, n1, i1, o1, c1⟩` from `adele_box a.re W1 h1`. Take `⟨T2, U2, n2, -, o2, c2⟩` from `adele_box a.imI W2 h2`. Take `⟨T3, U3, n3, -, o3, c3⟩` from `adele_box a.imJ W3 h3`. Take `⟨T4, U4, n4, -, o4, c4⟩` from `adele_box a.imK W4 h4`. Use `⟨T1 ∪ T2 ∪ T3 ∪ T4, fun u => {q | q.re ∈ U1 u ∧ q.imI ∈ U2 u ∧ q.imJ ∈ U3 u ∧ q.imK ∈ U4 u}, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `u`. Establish `m1 : {q : Q d β (Kp u) | q.re ∈ U1 u} ∈ 𝓝 (qmap (proj u) a)` using `(continuous_re (d := d) (β := β) (R := Kp u)).continuousAt.preimage_mem_nhds (n1 u)`. Establish `m2 : {q : Q d β (Kp u) | q.imI ∈ U2 u} ∈ 𝓝 (qmap (proj u) a)` using `(continuous_imI (d := d) (β := β) (R := Kp u)).continuousAt.preimage_mem_nhds (n2 u)`. Establish `m3 : {q : Q d β (Kp u) | q.imJ ∈ U3 u} ∈ 𝓝 (qmap (proj u) a)` using `(continuous_imJ (d := d) (β := β) (R := Kp u)).continuousAt.preimage_mem_nhds (n3 u)`. Establish `m4 : {q : Q d β (Kp u) | q.imK ∈ U4 u} ∈ 𝓝 (qmap (proj u) a)` using `(continuous_imK (d := d) (β := β) (R := Kp u)).continuousAt.preimage_mem_nhds (n4 u)`.

Use `filter_upwards [m1, m2, m3, m4] with q q1 q2 q3 q4 using ⟨q1, q2, q3, q4⟩`. Introduce `w`. Conclude with `Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (i1 w)))`. Introduce `b hb1 hb2`. Establish `t1 : T1 ⊆ T1 ∪ T2 ∪ T3 ∪ T4` using `fun u h => by simp [h]`.

Establish `t2 : T2 ⊆ T1 ∪ T2 ∪ T3 ∪ T4` using `fun u h => by simp [h]`. Establish `t3 : T3 ⊆ T1 ∪ T2 ∪ T3 ∪ T4` using `fun u h => by simp [h]`. Establish `t4 : T4 ⊆ T1 ∪ T2 ∪ T3 ∪ T4` using `fun u h => by simp [h]`. Establish `b1 : b.re ∈ W1` using `c1 b.re (fun u hu => (hb1 u (t1 hu)).1) fun v hv => by`. Distinguish the cases in `h : (Sum.inr v : Pl F) ∈ T1 ∪ T2 ∪ T3 ∪ T4`.

Conclude with `o1 v hv (hb1 _ h).1`. Conclude with `(hb2 v h).1`. Establish `b2 : b.imI ∈ W2` using `c2 b.imI (fun u hu => (hb1 u (t2 hu)).2.1) fun v hv => by`. Distinguish the cases in `h : (Sum.inr v : Pl F) ∈ T1 ∪ T2 ∪ T3 ∪ T4`. Conclude with `o2 v hv (hb1 _ h).2.1`.

Conclude with `(hb2 v h).2.1`. Establish `b3 : b.imJ ∈ W3` using `c3 b.imJ (fun u hu => (hb1 u (t3 hu)).2.2.1) fun v hv => by`. Distinguish the cases in `h : (Sum.inr v : Pl F) ∈ T1 ∪ T2 ∪ T3 ∪ T4`. Conclude with `o3 v hv (hb1 _ h).2.2.1`. Conclude with `(hb2 v h).2.2.1`.

Establish `b4 : b.imK ∈ W4` using `c4 b.imK (fun u hu => (hb1 u (t4 hu)).2.2.2) fun v hv => by`. Distinguish the cases in `h : (Sum.inr v : Pl F) ∈ T1 ∪ T2 ∪ T3 ∪ T4`. Conclude with `o4 v hv (hb1 _ h).2.2.2`. Conclude with `(hb2 v h).2.2.2`. Establish `hm : (b.re, b.imI, b.imJ, b.imK) ∈ e.symm ⁻¹' V` using `hs1 (Set.mk_mem_prod b1 (hs2 (Set.mk_mem_prod b2 (hs3 (Set.mk_mem_prod b3 b4)))))`.

Establish `hb : e.symm (b.re, b.imI, b.imJ, b.imK) = b` using `e.symm_apply_apply b`. Rewrite `hm` using `[Set.mem_preimage, hb]`. Conclude with `hm`.
-/
theorem basic_nhd {F : Type} [Field F] [NumberField F] (d β : F) (a : Q d β (AF F)) :
    ∀ V ∈ 𝓝 a,
      ∃ T : Finset (Pl F), ∃ U : (u : Pl F) → Set (Q d β (Kp u)),
        (∀ u, U u ∈ 𝓝 (qmap (proj u) a)) ∧ (∀ w : InfinitePlace F, (Sum.inl w : Pl F) ∈ T) ∧
        ∀ b : Q d β (AF F), (∀ u ∈ T, qmap (proj u) b ∈ U u) →
          (∀ v : HeightOneSpectrum (𝓞 F), (Sum.inr v : Pl F) ∉ T → IntQ v (qmap (proj (Sum.inr v)) b)) →
            b ∈ V := by
  classical
  intro V hV
  let e := qHomeo (d := d) (β := β) (R := AF F)
  have h0 : e.symm ⁻¹' V ∈ 𝓝 (a.re, a.imI, a.imJ, a.imK) := by
    refine e.symm.continuous.continuousAt.preimage_mem_nhds ?_
    have : e.symm (a.re, a.imI, a.imJ, a.imK) = a := e.symm_apply_apply a
    rw [this]
    exact hV
  obtain ⟨W1, h1, R1, hR1, hs1⟩ := mem_nhds_prod_iff.1 h0
  obtain ⟨W2, h2, R2, hR2, hs2⟩ := mem_nhds_prod_iff.1 hR1
  obtain ⟨W3, h3, W4, h4, hs3⟩ := mem_nhds_prod_iff.1 hR2
  obtain ⟨T1, U1, n1, i1, o1, c1⟩ := adele_box a.re W1 h1
  obtain ⟨T2, U2, n2, -, o2, c2⟩ := adele_box a.imI W2 h2
  obtain ⟨T3, U3, n3, -, o3, c3⟩ := adele_box a.imJ W3 h3
  obtain ⟨T4, U4, n4, -, o4, c4⟩ := adele_box a.imK W4 h4
  refine ⟨T1 ∪ T2 ∪ T3 ∪ T4,
    fun u => {q | q.re ∈ U1 u ∧ q.imI ∈ U2 u ∧ q.imJ ∈ U3 u ∧ q.imK ∈ U4 u}, ?_, ?_, ?_⟩
  · intro u
    have m1 : {q : Q d β (Kp u) | q.re ∈ U1 u} ∈ 𝓝 (qmap (proj u) a) :=
      (continuous_re (d := d) (β := β) (R := Kp u)).continuousAt.preimage_mem_nhds (n1 u)
    have m2 : {q : Q d β (Kp u) | q.imI ∈ U2 u} ∈ 𝓝 (qmap (proj u) a) :=
      (continuous_imI (d := d) (β := β) (R := Kp u)).continuousAt.preimage_mem_nhds (n2 u)
    have m3 : {q : Q d β (Kp u) | q.imJ ∈ U3 u} ∈ 𝓝 (qmap (proj u) a) :=
      (continuous_imJ (d := d) (β := β) (R := Kp u)).continuousAt.preimage_mem_nhds (n3 u)
    have m4 : {q : Q d β (Kp u) | q.imK ∈ U4 u} ∈ 𝓝 (qmap (proj u) a) :=
      (continuous_imK (d := d) (β := β) (R := Kp u)).continuousAt.preimage_mem_nhds (n4 u)
    filter_upwards [m1, m2, m3, m4] with q q1 q2 q3 q4 using ⟨q1, q2, q3, q4⟩
  · intro w
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (i1 w)))
  · intro b hb1 hb2
    have t1 : T1 ⊆ T1 ∪ T2 ∪ T3 ∪ T4 := fun u h => by simp [h]
    have t2 : T2 ⊆ T1 ∪ T2 ∪ T3 ∪ T4 := fun u h => by simp [h]
    have t3 : T3 ⊆ T1 ∪ T2 ∪ T3 ∪ T4 := fun u h => by simp [h]
    have t4 : T4 ⊆ T1 ∪ T2 ∪ T3 ∪ T4 := fun u h => by simp [h]
    have b1 : b.re ∈ W1 := c1 b.re (fun u hu => (hb1 u (t1 hu)).1) fun v hv => by
      by_cases h : (Sum.inr v : Pl F) ∈ T1 ∪ T2 ∪ T3 ∪ T4
      · exact o1 v hv (hb1 _ h).1
      · exact (hb2 v h).1
    have b2 : b.imI ∈ W2 := c2 b.imI (fun u hu => (hb1 u (t2 hu)).2.1) fun v hv => by
      by_cases h : (Sum.inr v : Pl F) ∈ T1 ∪ T2 ∪ T3 ∪ T4
      · exact o2 v hv (hb1 _ h).2.1
      · exact (hb2 v h).2.1
    have b3 : b.imJ ∈ W3 := c3 b.imJ (fun u hu => (hb1 u (t3 hu)).2.2.1) fun v hv => by
      by_cases h : (Sum.inr v : Pl F) ∈ T1 ∪ T2 ∪ T3 ∪ T4
      · exact o3 v hv (hb1 _ h).2.2.1
      · exact (hb2 v h).2.2.1
    have b4 : b.imK ∈ W4 := c4 b.imK (fun u hu => (hb1 u (t4 hu)).2.2.2) fun v hv => by
      by_cases h : (Sum.inr v : Pl F) ∈ T1 ∪ T2 ∪ T3 ∪ T4
      · exact o4 v hv (hb1 _ h).2.2.2
      · exact (hb2 v h).2.2.2
    have hm : (b.re, b.imI, b.imJ, b.imK) ∈ e.symm ⁻¹' V :=
      hs1 (Set.mk_mem_prod b1 (hs2 (Set.mk_mem_prod b2 (hs3 (Set.mk_mem_prod b3 b4)))))
    have hb : e.symm (b.re, b.imI, b.imJ, b.imK) = b := e.symm_apply_apply b
    rw [Set.mem_preimage, hb] at hm
    exact hm

end GlobalTheory.CompanionTheory.PlaneSA.Box
