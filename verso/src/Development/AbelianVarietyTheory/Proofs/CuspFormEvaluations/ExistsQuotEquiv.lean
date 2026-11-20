import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DatumInverseCharacter

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]`.
-/
theorem bar_bar (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

/- English proof (translation)
Establish `hc : (H.bar : 𝓞 E →+* 𝓞 E).comp (H.bar : 𝓞 E →+* 𝓞 E) = RingHom.id _` using `RingHom.ext fun a => bar_bar H a`. Establish `h2` using `Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hj`. Rewrite `h2` using `[Ideal.map_map, hc, Ideal.map_id]`. Conclude with `h2`.
-/
theorem bar_mem {I : Ideal (𝓞 E)} {j : 𝓞 E} (hj : j ∈ I.map (H.bar : 𝓞 E →+* 𝓞 E)) : H.bar j ∈ I := by
  have hc : (H.bar : 𝓞 E →+* 𝓞 E).comp (H.bar : 𝓞 E →+* 𝓞 E) = RingHom.id _ :=
    RingHom.ext fun a => bar_bar H a
  have h2 := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hj
  rw [Ideal.map_map, hc, Ideal.map_id] at h2
  exact h2

/- English proof (translation)
Take `⟨s, rfl⟩` from `Ideal.mem_span_singleton'.mp ht`. Establish `h : D.EF u ((s * (N : 𝓞 E)) • v) = D.EF (H.bar s • u) ((N : 𝓞 E) • v)`. Rewrite using `[D.adj, bar_bar, mul_smul]`. Rewrite using `[h, Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul]`. Conclude with `dvd_mul_right _ _`.
-/
theorem dvd_EF_smul (D : Datum H) {N : ℕ} {t : 𝓞 E} (ht : t ∈ Ideal.span {(N : 𝓞 E)}) (u v : D.La) :
    (N : ℤ) ∣ D.EF u (t • v) := by
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp ht
  have h : D.EF u ((s * (N : 𝓞 E)) • v) = D.EF (H.bar s • u) ((N : 𝓞 E) • v) := by
    rw [D.adj, bar_bar, mul_smul]
  rw [h, Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul]
  exact dvd_mul_right _ _

/- English proof (translation)
Use `Submodule.smul_induction_on (p := fun w => (N : ℤ) ∣ D.EF u (c • w)) hw ?_ ?_` and prove the remaining obligations. Introduce `a ha x _`. Rewrite using `[smul_smul]`. Apply `dvd_EF_smul D` to reduce the goal to its premises. Rewrite using `[← hI, _root_.mul_comm c a]`.

Conclude with `Ideal.mul_mem_mul ha hc`. Introduce `x y hx hy`. Rewrite using `[smul_add, map_add]`. Conclude with `dvd_add hx hy`.
-/
theorem dvd_right (D : Datum H) {N : ℕ} {I : Ideal (𝓞 E)}
    (hI : I * I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(N : 𝓞 E)}) {c : 𝓞 E}
    (hc : c ∈ I.map (H.bar : 𝓞 E →+* 𝓞 E)) (u : D.La) {w : D.La}
    (hw : w ∈ (I • ⊤ : Submodule (𝓞 E) D.La)) : (N : ℤ) ∣ D.EF u (c • w) := by
  refine Submodule.smul_induction_on (p := fun w => (N : ℤ) ∣ D.EF u (c • w)) hw ?_ ?_
  · intro a ha x _
    rw [smul_smul]
    apply dvd_EF_smul D
    rw [← hI, _root_.mul_comm c a]
    exact Ideal.mul_mem_mul ha hc
  · intro x y hx hy
    rw [smul_add, map_add]
    exact dvd_add hx hy

/- English proof (translation)
Use `Submodule.smul_induction_on (p := fun w => (N : ℤ) ∣ D.EF w (c • v)) hw ?_ ?_` and prove the remaining obligations. Introduce `a ha x _`. Rewrite using `[D.adj, smul_smul]`. Apply `dvd_EF_smul D` to reduce the goal to its premises. Rewrite using `[← hI]`.

Conclude with `Ideal.mul_mem_mul (bar_mem ha) hc`. Introduce `x y hx hy`. Rewrite using `[map_add, LinearMap.add_apply]`. Conclude with `dvd_add hx hy`.
-/
theorem dvd_left (D : Datum H) {N : ℕ} {I : Ideal (𝓞 E)}
    (hI : I * I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(N : 𝓞 E)}) {c : 𝓞 E}
    (hc : c ∈ I.map (H.bar : 𝓞 E →+* 𝓞 E)) (v : D.La) {w : D.La}
    (hw : w ∈ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) D.La)) : (N : ℤ) ∣ D.EF w (c • v) := by
  refine Submodule.smul_induction_on (p := fun w => (N : ℤ) ∣ D.EF w (c • v)) hw ?_ ?_
  · intro a ha x _
    rw [D.adj, smul_smul]
    apply dvd_EF_smul D
    rw [← hI]
    exact Ideal.mul_mem_mul (bar_mem ha) hc
  · intro x y hx hy
    rw [map_add, LinearMap.add_apply]
    exact dvd_add hx hy

/- English proof (translation)
Set `e` to `Equiv.ofBijective _ D.unimod`. Establish `hE : ∀ φ, D.EF (e.symm φ) = φ` using `fun φ => e.apply_symm_apply φ`. Use `⟨{ toFun := fun u => e.symm ((D.EF u).comp (f.restrictScalars ℤ)), map_add' := fun x y => D.unimod.1 ?_, map_smul' := fun a x => D.unimod.1 ?_ }, fun u v => ?_⟩` and prove the remaining obligations. Simplify using `only [hE, map_add, LinearMap.add_comp]`. Rewrite using `[hE]`.

Use extensionality with `v`. Simplify using `only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, RingHom.id_apply]`. Rewrite using `[D.adj, D.adj, LinearMap.congr_fun (hE _)]`. Simplify using `[map_smul]`. Conclude with `LinearMap.congr_fun (hE ((D.EF u).comp (f.restrictScalars ℤ))) v`.
-/
theorem exists_adjoint (D : Datum H) (f : D.La →ₗ[𝓞 E] D.La) :
    ∃ f' : D.La →ₗ[𝓞 E] D.La, ∀ u v, D.EF (f' u) v = D.EF u (f v) := by
  let e := Equiv.ofBijective _ D.unimod
  have hE : ∀ φ, D.EF (e.symm φ) = φ := fun φ => e.apply_symm_apply φ
  refine ⟨{ toFun := fun u => e.symm ((D.EF u).comp (f.restrictScalars ℤ)),
            map_add' := fun x y => D.unimod.1 ?_,
            map_smul' := fun a x => D.unimod.1 ?_ }, fun u v => ?_⟩
  · simp only [hE, map_add, LinearMap.add_comp]
  · rw [hE]
    ext v
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, RingHom.id_apply]
    rw [D.adj, D.adj, LinearMap.congr_fun (hE _)]
    simp [map_smul]
  · exact LinearMap.congr_fun (hE ((D.EF u).comp (f.restrictScalars ℤ))) v

/- English proof (translation)
Take `⟨b, hb⟩` from `D.unimod.2 ({ toFun := fun v => D.EF w v / n map_add' := fun x y => by`. Simplify using `only [map_add]`. Conclude with `Int.add_ediv_of_dvd_left (h x)`. Use the proof step `map_smul' := fun m x => by`. Simplify using `only [map_zsmul, smul_eq_mul, RingHom.id_apply]`.

Conclude with `Int.mul_ediv_assoc m (h x) } : D.La →ₗ[ℤ] ℤ)`. Use `⟨b, D.unimod.1 ?_⟩` and prove the remaining obligations. Use extensionality with `v`. Rewrite using `[map_nsmul, LinearMap.smul_apply, hb]`. Simplify using `only [LinearMap.coe_mk, AddHom.coe_mk, nsmul_eq_mul]`.

Conclude with `(Int.mul_ediv_cancel' (h v)).symm`.
-/
theorem modN_of_dvd (D : Datum H) {n : ℕ} (hn : 0 < n) {w : D.La} (h : ∀ v, (n : ℤ) ∣ D.EF w v) :
    D.ModN n w := by
  obtain ⟨b, hb⟩ := D.unimod.2
    ({ toFun := fun v => D.EF w v / n
       map_add' := fun x y => by
         simp only [map_add]
         exact Int.add_ediv_of_dvd_left (h x)
       map_smul' := fun m x => by
         simp only [map_zsmul, smul_eq_mul, RingHom.id_apply]
         exact Int.mul_ediv_assoc m (h x) } : D.La →ₗ[ℤ] ℤ)
  refine ⟨b, D.unimod.1 ?_⟩
  ext v
  rw [map_nsmul, LinearMap.smul_apply, hb]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, nsmul_eq_mul]
  exact (Int.mul_ediv_cancel' (h v)).symm

/- English proof (translation)
Take `⟨b, rfl⟩` from `h`. Rewrite using `[map_nsmul, nsmul_eq_mul]`. Conclude with `dvd_mul_right _ _`.
-/
theorem dvd_of_modN (D : Datum H) {n : ℕ} (u : D.La) {w : D.La} (h : D.ModN n w) : (n : ℤ) ∣ D.EF u w := by
  obtain ⟨b, rfl⟩ := h
  rw [map_nsmul, nsmul_eq_mul]
  exact dvd_mul_right _ _

/- English proof (translation)
Take `⟨b, rfl⟩` from `h`. Rewrite using `[← Nat.cast_smul_eq_nsmul (𝓞 E)]`. Conclude with `Submodule.smul_mem_smul hK Submodule.mem_top`.
-/
theorem mem_of_modN (D : Datum H) {n : ℕ} {K : Ideal (𝓞 E)} (hK : (n : 𝓞 E) ∈ K) {w : D.La}
    (h : D.ModN n w) : w ∈ (K • ⊤ : Submodule (𝓞 E) D.La) := by
  obtain ⟨b, rfl⟩ := h
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul hK Submodule.mem_top

/- English proof (translation)
Establish `hle : ∀ φ : D.La →ₗ[𝓞 E] D.La, (K • ⊤ : Submodule (𝓞 E) D.La) ≤ (K • ⊤ : Submodule (𝓞 E) D.La).comap φ`. Introduce `φ`. Rewrite using `[Submodule.smul_le]`. Introduce `r hr x _`. Rewrite using `[Submodule.mem_comap, map_smul]`.

Conclude with `Submodule.smul_mem_smul hr Submodule.mem_top`. Use `⟨LinearEquiv.ofLinear ((K • ⊤ : Submodule (𝓞 E) D.La).mapQ _ f (hle f)) ((K • ⊤ : Submodule (𝓞 E) D.La).mapQ _ g (hle g)) ?_ ?_, fun a => rfl⟩` and prove the remaining obligations. Use extensionality with `a`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.id_apply]`. Conclude with `(Submodule.Quotient.eq _).2 (mem_of_modN D hK (h a).2)`.

Use extensionality with `a`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.id_apply]`. Conclude with `(Submodule.Quotient.eq _).2 (mem_of_modN D hK (h a).1)`.
-/
theorem exists_quot_equiv (D : Datum H) {n : ℕ} {K : Ideal (𝓞 E)} (hK : (n : 𝓞 E) ∈ K)
    (f g : D.La →ₗ[𝓞 E] D.La) (h : ∀ a, D.ModN n (g (f a) - a) ∧ D.ModN n (f (g a) - a)) :
    ∃ k : (D.La ⧸ (K • ⊤ : Submodule (𝓞 E) D.La)) ≃ₗ[𝓞 E] (D.La ⧸ (K • ⊤ : Submodule (𝓞 E) D.La)),
      ∀ a, k (Submodule.Quotient.mk a) = Submodule.Quotient.mk (f a) := by
  have hle : ∀ φ : D.La →ₗ[𝓞 E] D.La,
      (K • ⊤ : Submodule (𝓞 E) D.La) ≤ (K • ⊤ : Submodule (𝓞 E) D.La).comap φ := by
    intro φ
    rw [Submodule.smul_le]
    intro r hr x _
    rw [Submodule.mem_comap, map_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  refine ⟨LinearEquiv.ofLinear ((K • ⊤ : Submodule (𝓞 E) D.La).mapQ _ f (hle f))
    ((K • ⊤ : Submodule (𝓞 E) D.La).mapQ _ g (hle g)) ?_ ?_, fun a => rfl⟩
  · ext a
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      LinearMap.id_apply]
    exact (Submodule.Quotient.eq _).2 (mem_of_modN D hK (h a).2)
  · ext a
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      LinearMap.id_apply]
    exact (Submodule.Quotient.eq _).2 (mem_of_modN D hK (h a).1)

/- English proof (translation)
Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`. Rewrite `hz` using `[zero_pow hN.ne']`. Conclude with `zero_ne_one hz`. Take `⟨k, hk⟩` from `h`.

Rewrite using `[show a = b + N * k by linarith, zpow_add₀ hz0, zpow_mul, zpow_natCast, hz, one_zpow, _root_.mul_one]`.
-/
theorem zpow_congr {F : Type} [Field F] {z : F} {N : ℕ} (hN : 0 < N) (hz : z ^ N = 1) {a b : ℤ}
    (h : (N : ℤ) ∣ a - b) : z ^ a = z ^ b := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hz
    exact zero_ne_one hz
  obtain ⟨k, hk⟩ := h
  rw [show a = b + N * k by linarith, zpow_add₀ hz0, zpow_mul, zpow_natCast, hz, one_zpow, _root_.mul_one]

/- English proof (translation)
The claim follows from `(Complex.isPrimitiveRoot_exp n hn.ne').pow_eq_one`.
-/
theorem zeta_pow {n : ℕ} (hn : 0 < n) : zeta n ^ n = 1 := (Complex.isPrimitiveRoot_exp n hn.ne').pow_eq_one

/- English proof (translation)
Establish `hd : N ∣ l.M'` using `hN.trans (Nat.dvd_lcm_left l.M l.A)`. Establish `hpos : 0 < l.M'` using `Nat.lcm_pos (by have := l.three_le; omega) l.A_pos`. Rewrite using `[← pow_mul, Nat.div_mul_cancel hd]`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using zeta_pow hpos`.
-/
theorem root_pow {l : Level H} (c : Coeff l) {N : ℕ} (hN : N ∣ l.M) :
    ((⟨zeta l.M', c.zeta_mem⟩ : c.F) ^ (l.M' / N)) ^ N = 1 := by
  have hd : N ∣ l.M' := hN.trans (Nat.dvd_lcm_left l.M l.A)
  have hpos : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  rw [← pow_mul, Nat.div_mul_cancel hd]
  apply Subtype.ext
  simpa using zeta_pow hpos

/- English proof (translation)
Unfold `cHalf`. Use `split_ifs with h`. Conclude with `h.choose_spec.1`. Conclude with `zero_mem _`.
-/
theorem cHalf_mem (I : Ideal (𝓞 E)) : cHalf H I ∈ I.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  unfold cHalf
  split_ifs with h
  · exact h.choose_spec.1
  · exact zero_mem _

/- English proof (translation)
Unfold `cSep`. Use `split_ifs with h`. Conclude with `h.choose_spec.1`. Conclude with `zero_mem _`.
-/
theorem cSep_mem (l : Level H) : cSep l ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  unfold cSep
  split_ifs with h
  · exact h.choose_spec.1
  · exact zero_mem _

/- English proof (translation)
The claim follows from `Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)`.
-/
theorem qRep_spec {D : Datum H} {K : Submodule (𝓞 E) D.La} (q : D.La ⧸ K) :
    (Submodule.Quotient.mk (qRep q) : D.La ⧸ K) = q := Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)

/- English proof (translation)
The claim follows from `Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)`.
-/
theorem levRep_spec {D : Datum H} {l : Level H} (q : LevQ D l) :
    (Submodule.Quotient.mk (levRep q) : LevQ D l) = q := Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)

/- English proof (translation)
Establish `h1` using `l₂.prod`. Rewrite `h1` using `[hb, Ideal.map_mul, hM, Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton, _root_.mul_mul_mul_comm, l.prod]`. Establish `h0 : Ideal.span {(l.M : 𝓞 E)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Use `l.three_le` as an intermediate fact.

Conclude with `(by omega : l.M ≠ 0)` after adjusting the coercions. Conclude with `mul_left_cancel₀ h0 h1`.
-/
theorem half_prod {l l₂ : Level H} {pd : ℕ} {I : Ideal (𝓞 E)} (hM : l₂.M = l.M * pd) (hb : l₂.Mb = l.Mb * I) :
    I * I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(pd : 𝓞 E)} := by
  have h1 := l₂.prod
  rw [hb, Ideal.map_mul, hM, Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton,
    _root_.mul_mul_mul_comm, l.prod] at h1
  have h0 : Ideal.span {(l.M : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    have := l.three_le
    exact_mod_cast (by omega : l.M ≠ 0)
  exact mul_left_cancel₀ h0 h1
set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c n d hM hcop hb hsup hdvd ph ψ x₀ hpin g hg`. Take `⟨-, hgM, -⟩` from `hg`. Establish `hI` using `half_prod hM hb`. Establish `hpdII : (d.pd : 𝓞 E) ∈ d.I * d.I.map (H.bar : 𝓞 E →+* 𝓞 E)`. Rewrite using `[hI]`.

Conclude with `Ideal.mem_span_singleton_self _`. Establish `hpdI : (d.pd : 𝓞 E) ∈ d.I` using `(Ideal.mul_le_left : d.I * d.I.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ d.I) hpdII`. Establish `hpdJ : (d.pd : 𝓞 E) ∈ d.I.map (H.bar : 𝓞 E →+* 𝓞 E)` using `(Ideal.mul_le_right : d.I * d.I.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ d.I.map (H.bar : 𝓞 E →+* 𝓞 E)) hpdII`. Establish `hM₂I : (d.l₂.M : 𝓞 E) ∈ d.I`. Rewrite using `[hM, Nat.cast_mul]`.

Conclude with `Ideal.mul_mem_left _ _ hpdI`. Establish `hM₂J : (d.l₂.M : 𝓞 E) ∈ d.I.map (H.bar : 𝓞 E →+* 𝓞 E)`. Rewrite using `[hM, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_left _ _ hpdJ`. Establish `hM₂B : (d.l₂.M : 𝓞 E) ∈ d.l₂.Mb`.

Establish `: (d.l₂.M : 𝓞 E) ∈ d.l₂.Mb * d.l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)`. Rewrite using `[d.l₂.prod]`. Conclude with `Ideal.mem_span_singleton_self _`. Conclude with `(Ideal.mul_le_left : d.l₂.Mb * d.l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ d.l₂.Mb) this`. Establish `hMB : (l.M : 𝓞 E) ∈ l.Mb`.

Establish `: (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)`. Rewrite using `[l.prod]`. Conclude with `Ideal.mem_span_singleton_self _`. Conclude with `(Ideal.mul_le_left : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb) this`. Establish `hM₂pos : 0 < d.l₂.M` using `by have := d.l₂.three_le; omega`.

Establish `hMpos : 0 < l.M` using `by have := l.three_le; omega`. Establish `hpdpos : 0 < d.pd`. Break down `Nat.eq_zero_or_pos d.pd with h0 | h0` into its components or cases. Rewrite `hM` using `[h0, Nat.mul_zero]`. Use `d.l₂.three_le` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Conclude with `h0`. Take `⟨G, hG⟩` from `g.inv d.l₂.M hM₂pos`. Take `⟨kI, hkI⟩` from `exists_quot_equiv Dw hM₂I (g.f d.l₂.M) G hG`. Take `⟨k₂, hk₂⟩` from `exists_quot_equiv Dw hM₂B (g.f d.l₂.M) G hG`.

Take `⟨F', hF'⟩` from `exists_adjoint Dw (g.f d.l₂.M)`. Take `⟨G', hG'⟩` from `exists_adjoint Dw G`. Establish `hGF' : ∀ a, Dw.ModN d.l₂.M (G' (F' a) - a) ∧ Dw.ModN d.l₂.M (F' (G' a) - a)`. Introduce `a`. Prove the components needed by the constructor for the conclusion.

Use `modN_of_dvd Dw hM₂pos fun v => ?_` and prove the remaining obligations. Rewrite using `[map_sub, LinearMap.sub_apply, hG', hF', ← map_sub]`. Conclude with `dvd_of_modN Dw a (hG v).2`. Use `modN_of_dvd Dw hM₂pos fun v => ?_` and prove the remaining obligations. Rewrite using `[map_sub, LinearMap.sub_apply, hF', hG', ← map_sub]`.

Conclude with `dvd_of_modN Dw a (hG v).1`. Take `⟨kst, hkst⟩` from `exists_quot_equiv Dw hM₂J F' G' hGF'`. Establish `hle₂ : d.l₂.Mb ≤ l.Mb`. Rewrite using `[hb]`. Conclude with `Ideal.mul_le_left`.

Establish `hle₂I : d.l₂.Mb ≤ d.I`. Rewrite using `[hb]`. Conclude with `Ideal.mul_le_right`. Establish `hrep : ∀ y : LevQ Dw d.l₂, g.f d.l₂.M (levRep (k₂.symm y)) - levRep y ∈ (d.l₂.Mb • ⊤ : Submodule (𝓞 E) Dw.La)`. Introduce `y`.

Apply `(Submodule.Quotient.eq _).1` to reduce the goal to its premises. Rewrite using `[← hk₂, levRep_spec, levRep_spec, LinearEquiv.apply_symm_apply]`. Establish `hdiffL : ∀ y : LevQ Dw d.l₂, levRep (k₂.symm y) - levRep y ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La)`. Introduce `y`. Establish `e1 : g.f d.l₂.M (levRep (k₂.symm y)) - levRep (k₂.symm y) ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La)`.

Establish `t` using `g.tower l.M d.pd hMpos hpdpos (levRep (k₂.symm y))`. Rewrite `t` using `[← hM]`. Rewrite using `[← sub_add_sub_cancel (g.f d.l₂.M (levRep (k₂.symm y))) (g.f l.M (levRep (k₂.symm y))) (levRep (k₂.symm y))]`. Conclude with `add_mem (mem_of_modN Dw hMB t) (hgM _)`. Establish `e2` using `Submodule.smul_mono_left hle₂ (hrep y)`.

Rewrite using `[show levRep (k₂.symm y) - levRep y = (g.f d.l₂.M (levRep (k₂.symm y)) - levRep y) - (g.f d.l₂.M (levRep (k₂.symm y)) - levRep (k₂.symm y)) by abel]`. Conclude with `sub_mem e2 e1`. Establish `hz : zetaM c ^ l.M = 1`. Unfold `zetaM`. Conclude with `root_pow c dvd_rfl`.

Establish `hpair : ∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂), zetaM c ^ pairL (l` using `l) x0 (fun b => levRep (k₂.symm (q b))) = zetaM c ^ pairL (l := l) x0 (fun b => levRep (q b)) := by`. Introduce `x0 q`. Apply `zpow_congr hMpos hz` to reduce the goal to its premises. Unfold `pairL`. Rewrite using `[← Finset.sum_sub_distrib]`.

Apply `Finset.dvd_sum` to reduce the goal to its premises. Introduce `b _`. Rewrite using `[← map_sub, ← smul_sub]`. Conclude with `dvd_right Dw l.prod (cSep_mem l) (x0 b) (hdiffL (q b))`. Establish `hp` using `hpin`.

Unfold `DeltaDat.PhiPin at hp`. Take `⟨-, -, hrule, -, -, hsum⟩` from `hp`. Establish `hcompat : ∀ u v : Dw.La, ((d.pd : ℤ) ∣ Dw.EF (qRep (kst (Submodule.Quotient.mk u))) (cHalf H d.I • v) - Dw.EF u (cHalf H d.I • qRep (kI (Submodule.Quotient.mk v))))`. Introduce `u v`. Establish `m1 : qRep (kst (Submodule.Quotient.mk u)) - F' u ∈ (d.I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La)`.

Apply `(Submodule.Quotient.eq _).1` to reduce the goal to its premises. Rewrite using `[qRep_spec, hkst]`. Establish `m2 : g.f d.l₂.M v - qRep (kI (Submodule.Quotient.mk v)) ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La)`. Apply `(Submodule.Quotient.eq _).1` to reduce the goal to its premises. Rewrite using `[qRep_spec, hkI]`.

Establish `key : Dw.EF (F' u) (cHalf H d.I • v) = Dw.EF u (cHalf H d.I • g.f d.l₂.M v)`. Rewrite using `[hF', map_smul]`. Establish `eq : Dw.EF (qRep (kst (Submodule.Quotient.mk u))) (cHalf H d.I • v) - Dw.EF u (cHalf H d.I • qRep (kI (Submodule.Quotient.mk v))) = Dw.EF (qRep (kst (Submodule.Quotient.mk u)) - F' u) (cHalf H d.I • v) + Dw.EF u (cHalf H d.I • (g.f d.l₂.M v - qRep (kI (Submodule.Quotient.mk v))))`. Rewrite using `[map_sub, LinearMap.sub_apply, smul_sub, map_sub (Dw.EF u), key]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[eq]`. Conclude with `dvd_add (dvd_left Dw hI (cHalf_mem d.I) v m1) (dvd_right Dw hI (cHalf_mem d.I) u m2)`. Establish `hphi : ∀ q : Fin n → LevQ Dw d.l₂, d.eF (d.φδ (fun b => k₂.symm (q b))) = d.eF (((ψ kI)⁻¹ : c.Fˣ) : c.F) * d.eF (d.φδ q)`. Introduce `q`. Rewrite using `[hsum, hsum, mul_finsum, ← finsum_comp_equiv (Equiv.piCongrRight fun _ : Fin n => kst.toEquiv)]`.

Establish `hΦ : ∀ x : Fin n → LaJ Xo c d, (Equiv.piCongrRight fun _ : Fin n => kst.toEquiv) x = fun b => kst (x b)` using `fun x => rfl`. Apply `finsum_congr` to reduce the goal to its premises. Introduce `x`. Rewrite using `[hΦ]`. Establish `hZ : ((⟨zeta d.l₂.M', d.c₂.zeta_mem⟩ : d.c₂.F) ^ (d.l₂.M' / d.pd)) ^ (∑ b, Dw.EF (qRep (kst (x b))) (cHalf H d.I • levRep (k₂.symm (q b)))) = ((⟨zeta d.l₂.M', d.c₂.zeta_mem⟩ : d.c₂.F) ^ (d.l₂.M' / d.pd)) ^ (∑ b, Dw.EF (qRep (x b)) (cHalf H d.I • levRep (q b)))`.

Apply `zpow_congr hpdpos (root_pow d.c₂ (Dvd.intro_left _ hM.symm))` to reduce the goal to its premises. Rewrite using `[← Finset.sum_sub_distrib]`. Apply `Finset.dvd_sum` to reduce the goal to its premises. Introduce `b _`. Establish `hu : kst (x b) = kst (Submodule.Quotient.mk (qRep (x b)))` using `by rw [qRep_spec]`.

Establish `m3 : qRep (kI (Submodule.Quotient.mk (levRep (k₂.symm (q b))))) - levRep (q b) ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La)`. Establish `a1 : qRep (kI (Submodule.Quotient.mk (levRep (k₂.symm (q b))))) - g.f d.l₂.M (levRep (k₂.symm (q b))) ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La)`. Apply `(Submodule.Quotient.eq _).1` to reduce the goal to its premises. Rewrite using `[qRep_spec, hkI]`. Rewrite using `[← sub_add_sub_cancel _ (g.f d.l₂.M (levRep (k₂.symm (q b)))) _]`.

Conclude with `add_mem a1 (Submodule.smul_mono_left hle₂I (hrep (q b)))`. Rewrite using `[hu]`. Establish `eq : Dw.EF (qRep (kst (Submodule.Quotient.mk (qRep (x b))))) (cHalf H d.I • levRep (k₂.symm (q b))) - Dw.EF (qRep (x b)) (cHalf H d.I • levRep (q b)) = (Dw.EF (qRep (kst (Submodule.Quotient.mk (qRep (x b))))) (cHalf H d.I • levRep (k₂.symm (q b))) - Dw.EF (qRep (x b)) (cHalf H d. …`. Rewrite using `[smul_sub, map_sub]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[eq]`. Conclude with `dvd_add (hcompat _ _) (dvd_right Dw hI (cHalf_mem d.I) _ m3)`. Rewrite using `[hrule kI kst hcompat x, map_mul, _root_.mul_assoc, hZ]`. Use `⟨kI, k₂.toEquiv, fun a => (hkI a).symm, fun a => hk₂ a, ?_⟩` and prove the remaining obligations. Introduce `x0 q`.

Use `show d.eF (zetaM c ^ pairL (l := l) x0 (fun b => levRep (k₂.symm (q b))) * d.φδ (fun b => k₂.symm (q b))) = d.eF (((ψ kI)⁻¹ : c.Fˣ) : c.F) * d.eF (zetaM c ^ pairL (l := l) x0 (fun b => levRep (q b)) * d.φδ q)`. Rewrite using `[map_mul, map_mul, hpair x0 q, hphi q]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem datum_inv_char : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.l₂.M = l.M * d.pd → Nat.Coprime d.pd l.M → d.l₂.Mb = l.Mb * d.I → d.I ⊔ d.I.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ → l.Dvd d.l₂ → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ g : Sim Dw, g.InGam l d.l₂ → ∃ (kI : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) (σq : LevQ Dw d.l₂ ≃ LevQ Dw d.l₂), (∀ a : Dw.La, (Submodule.Quotient.mk (g.f d.l₂.M a) : LaI Xo c d) = kI (Submodule.Quotient.mk a)) ∧ (∀ a, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk (g.f d.l₂.M a)) ∧ ∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂), d.w x0 (fun b => σq.symm (q b)) = d.eF (((ψ kI)⁻¹ : c.Fˣ) : c.F) * d.w x0 q := by
  intro E _ _ _ H Dw l Xo c n d hM hcop hb hsup hdvd ph ψ x₀ hpin g hg
  obtain ⟨-, hgM, -⟩ := hg
  have hI := half_prod hM hb
  have hpdII : (d.pd : 𝓞 E) ∈ d.I * d.I.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [hI]
    exact Ideal.mem_span_singleton_self _
  have hpdI : (d.pd : 𝓞 E) ∈ d.I :=
    (Ideal.mul_le_left : d.I * d.I.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ d.I) hpdII
  have hpdJ : (d.pd : 𝓞 E) ∈ d.I.map (H.bar : 𝓞 E →+* 𝓞 E) :=
    (Ideal.mul_le_right : d.I * d.I.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ d.I.map (H.bar : 𝓞 E →+* 𝓞 E)) hpdII
  have hM₂I : (d.l₂.M : 𝓞 E) ∈ d.I := by
    rw [hM, Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ hpdI
  have hM₂J : (d.l₂.M : 𝓞 E) ∈ d.I.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [hM, Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ hpdJ
  have hM₂B : (d.l₂.M : 𝓞 E) ∈ d.l₂.Mb := by
    have : (d.l₂.M : 𝓞 E) ∈ d.l₂.Mb * d.l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [d.l₂.prod]
      exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_left : d.l₂.Mb * d.l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ d.l₂.Mb) this
  have hMB : (l.M : 𝓞 E) ∈ l.Mb := by
    have : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]
      exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_left : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb) this
  have hM₂pos : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  have hMpos : 0 < l.M := by have := l.three_le; omega
  have hpdpos : 0 < d.pd := by
    rcases Nat.eq_zero_or_pos d.pd with h0 | h0
    · rw [h0, Nat.mul_zero] at hM
      have := d.l₂.three_le
      omega
    · exact h0
  obtain ⟨G, hG⟩ := g.inv d.l₂.M hM₂pos
  obtain ⟨kI, hkI⟩ := exists_quot_equiv Dw hM₂I (g.f d.l₂.M) G hG
  obtain ⟨k₂, hk₂⟩ := exists_quot_equiv Dw hM₂B (g.f d.l₂.M) G hG
  obtain ⟨F', hF'⟩ := exists_adjoint Dw (g.f d.l₂.M)
  obtain ⟨G', hG'⟩ := exists_adjoint Dw G
  have hGF' : ∀ a, Dw.ModN d.l₂.M (G' (F' a) - a) ∧ Dw.ModN d.l₂.M (F' (G' a) - a) := by
    intro a
    constructor
    · refine modN_of_dvd Dw hM₂pos fun v => ?_
      rw [map_sub, LinearMap.sub_apply, hG', hF', ← map_sub]
      exact dvd_of_modN Dw a (hG v).2
    · refine modN_of_dvd Dw hM₂pos fun v => ?_
      rw [map_sub, LinearMap.sub_apply, hF', hG', ← map_sub]
      exact dvd_of_modN Dw a (hG v).1
  obtain ⟨kst, hkst⟩ := exists_quot_equiv Dw hM₂J F' G' hGF'
  have hle₂ : d.l₂.Mb ≤ l.Mb := by
    rw [hb]
    exact Ideal.mul_le_left
  have hle₂I : d.l₂.Mb ≤ d.I := by
    rw [hb]
    exact Ideal.mul_le_right
  have hrep : ∀ y : LevQ Dw d.l₂, g.f d.l₂.M (levRep (k₂.symm y)) - levRep y ∈
      (d.l₂.Mb • ⊤ : Submodule (𝓞 E) Dw.La) := by
    intro y
    apply (Submodule.Quotient.eq _).1
    rw [← hk₂, levRep_spec, levRep_spec, LinearEquiv.apply_symm_apply]
  have hdiffL : ∀ y : LevQ Dw d.l₂, levRep (k₂.symm y) - levRep y ∈
      (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) := by
    intro y
    have e1 : g.f d.l₂.M (levRep (k₂.symm y)) - levRep (k₂.symm y) ∈
        (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) := by
      have t := g.tower l.M d.pd hMpos hpdpos (levRep (k₂.symm y))
      rw [← hM] at t
      rw [← sub_add_sub_cancel (g.f d.l₂.M (levRep (k₂.symm y))) (g.f l.M (levRep (k₂.symm y)))
        (levRep (k₂.symm y))]
      exact add_mem (mem_of_modN Dw hMB t) (hgM _)
    have e2 := Submodule.smul_mono_left hle₂ (hrep y)
    rw [show levRep (k₂.symm y) - levRep y = (g.f d.l₂.M (levRep (k₂.symm y)) - levRep y) -
      (g.f d.l₂.M (levRep (k₂.symm y)) - levRep (k₂.symm y)) by abel]
    exact sub_mem e2 e1
  have hz : zetaM c ^ l.M = 1 := by
    unfold zetaM
    exact root_pow c dvd_rfl
  have hpair : ∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂),
      zetaM c ^ pairL (l := l) x0 (fun b => levRep (k₂.symm (q b))) =
        zetaM c ^ pairL (l := l) x0 (fun b => levRep (q b)) := by
    intro x0 q
    apply zpow_congr hMpos hz
    unfold pairL
    rw [← Finset.sum_sub_distrib]
    apply Finset.dvd_sum
    intro b _
    rw [← map_sub, ← smul_sub]
    exact dvd_right Dw l.prod (cSep_mem l) (x0 b) (hdiffL (q b))
  have hp := hpin
  unfold DeltaDat.PhiPin at hp
  obtain ⟨-, -, hrule, -, -, hsum⟩ := hp
  have hcompat : ∀ u v : Dw.La, ((d.pd : ℤ) ∣ Dw.EF (qRep (kst (Submodule.Quotient.mk u))) (cHalf H d.I • v) -
      Dw.EF u (cHalf H d.I • qRep (kI (Submodule.Quotient.mk v)))) := by
    intro u v
    have m1 : qRep (kst (Submodule.Quotient.mk u)) - F' u ∈
        (d.I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La) := by
      apply (Submodule.Quotient.eq _).1
      rw [qRep_spec, hkst]
    have m2 : g.f d.l₂.M v - qRep (kI (Submodule.Quotient.mk v)) ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La) := by
      apply (Submodule.Quotient.eq _).1
      rw [qRep_spec, hkI]
    have key : Dw.EF (F' u) (cHalf H d.I • v) = Dw.EF u (cHalf H d.I • g.f d.l₂.M v) := by
      rw [hF', map_smul]
    have eq : Dw.EF (qRep (kst (Submodule.Quotient.mk u))) (cHalf H d.I • v) -
        Dw.EF u (cHalf H d.I • qRep (kI (Submodule.Quotient.mk v))) =
        Dw.EF (qRep (kst (Submodule.Quotient.mk u)) - F' u) (cHalf H d.I • v) +
        Dw.EF u (cHalf H d.I • (g.f d.l₂.M v - qRep (kI (Submodule.Quotient.mk v)))) := by
      rw [map_sub, LinearMap.sub_apply, smul_sub, map_sub (Dw.EF u), key]
      ring
    rw [eq]
    exact dvd_add (dvd_left Dw hI (cHalf_mem d.I) v m1) (dvd_right Dw hI (cHalf_mem d.I) u m2)
  have hphi : ∀ q : Fin n → LevQ Dw d.l₂, d.eF (d.φδ (fun b => k₂.symm (q b))) =
      d.eF (((ψ kI)⁻¹ : c.Fˣ) : c.F) * d.eF (d.φδ q) := by
    intro q
    rw [hsum, hsum, mul_finsum, ← finsum_comp_equiv (Equiv.piCongrRight fun _ : Fin n => kst.toEquiv)]
    have hΦ : ∀ x : Fin n → LaJ Xo c d,
        (Equiv.piCongrRight fun _ : Fin n => kst.toEquiv) x = fun b => kst (x b) := fun x => rfl
    apply finsum_congr
    intro x
    rw [hΦ]
    have hZ : ((⟨zeta d.l₂.M', d.c₂.zeta_mem⟩ : d.c₂.F) ^ (d.l₂.M' / d.pd)) ^
        (∑ b, Dw.EF (qRep (kst (x b))) (cHalf H d.I • levRep (k₂.symm (q b)))) =
        ((⟨zeta d.l₂.M', d.c₂.zeta_mem⟩ : d.c₂.F) ^ (d.l₂.M' / d.pd)) ^
        (∑ b, Dw.EF (qRep (x b)) (cHalf H d.I • levRep (q b))) := by
      apply zpow_congr hpdpos (root_pow d.c₂ (Dvd.intro_left _ hM.symm))
      rw [← Finset.sum_sub_distrib]
      apply Finset.dvd_sum
      intro b _
      have hu : kst (x b) = kst (Submodule.Quotient.mk (qRep (x b))) := by rw [qRep_spec]
      have m3 : qRep (kI (Submodule.Quotient.mk (levRep (k₂.symm (q b))))) - levRep (q b) ∈
          (d.I • ⊤ : Submodule (𝓞 E) Dw.La) := by
        have a1 : qRep (kI (Submodule.Quotient.mk (levRep (k₂.symm (q b))))) -
            g.f d.l₂.M (levRep (k₂.symm (q b))) ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La) := by
          apply (Submodule.Quotient.eq _).1
          rw [qRep_spec, hkI]
        rw [← sub_add_sub_cancel _ (g.f d.l₂.M (levRep (k₂.symm (q b)))) _]
        exact add_mem a1 (Submodule.smul_mono_left hle₂I (hrep (q b)))
      rw [hu]
      have eq : Dw.EF (qRep (kst (Submodule.Quotient.mk (qRep (x b))))) (cHalf H d.I • levRep (k₂.symm (q b))) -
          Dw.EF (qRep (x b)) (cHalf H d.I • levRep (q b)) =
          (Dw.EF (qRep (kst (Submodule.Quotient.mk (qRep (x b))))) (cHalf H d.I • levRep (k₂.symm (q b))) -
            Dw.EF (qRep (x b)) (cHalf H d.I • qRep (kI (Submodule.Quotient.mk (levRep (k₂.symm (q b))))))) +
          Dw.EF (qRep (x b)) (cHalf H d.I •
            (qRep (kI (Submodule.Quotient.mk (levRep (k₂.symm (q b))))) - levRep (q b))) := by
        rw [smul_sub, map_sub]
        ring
      rw [eq]
      exact dvd_add (hcompat _ _) (dvd_right Dw hI (cHalf_mem d.I) _ m3)
    rw [hrule kI kst hcompat x, map_mul, _root_.mul_assoc, hZ]
  refine ⟨kI, k₂.toEquiv, fun a => (hkI a).symm, fun a => hk₂ a, ?_⟩
  intro x0 q
  show d.eF (zetaM c ^ pairL (l := l) x0 (fun b => levRep (k₂.symm (q b))) * d.φδ (fun b => k₂.symm (q b))) =
    d.eF (((ψ kI)⁻¹ : c.Fˣ) : c.F) * d.eF (zetaM c ^ pairL (l := l) x0 (fun b => levRep (q b)) * d.φδ q)
  rw [map_mul, map_mul, hpair x0 q, hphi q]
  ring

end GlobalTheory.DatumInverseCharacter
