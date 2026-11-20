import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartExponentialToroidalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HorizontalFunctionMatrixRelation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HorizontalCoordinateLatticeIsometryDetOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatSectionIsFlat

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DetLine

section Level

open GlobalTheory.ShFam.HorIso

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

/- English proof (translation)
Take `⟨k, hk, hdk⟩` from `NumberField.Embeddings.pow_eq_one_of_norm_eq_one E ℂ d.isIntegral_coe hd`. Establish `hfin : IsOfFinOrder d` using `isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, by ext; simpa using hdk⟩`. Assume the negation of the conclusion as `hne`. Take `⟨p, hp, hpd⟩` from `Nat.exists_prime_and_dvd (mt orderOf_eq_one_iff.1 hne)`. Use `set z := d ^ (orderOf d / p) with hz`.

Establish `ho : orderOf z = p` using `orderOf_pow_orderOf_div hfin.orderOf_pos.ne' hpd`. Establish `hz1 : z - 1 ∈ l.Mb` using `Ideal.mem_of_dvd _ (sub_one_dvd_pow_sub_one d _) hm`. Establish `hprim : IsPrimitiveRoot z p` using `ho ▸ IsPrimitiveRoot.orderOf z`. Establish `hn : ∀ a : ℕ, Algebra.norm ℤ (a : 𝓞 E) = (a : ℤ) ^ Module.finrank ℤ (𝓞 E)` using `fun a => by`. Simplify using `using Algebra.norm_algebraMap (R := ℤ) (S := 𝓞 E) (a : ℤ)`.

Establish `hdiv : ∀ a b : ℕ, (a : 𝓞 E) ∣ b → a ∣ b` using `fun a b h => by`. Establish `h3` using `map_dvd (Algebra.norm ℤ) h`. Rewrite `h3` using `[hn, hn, Int.pow_dvd_pow_iff Module.finrank_pos.ne']`. Conclude with `h3` after adjusting the coercions. Take `⟨n, rfl⟩ : ∃ n, p = n + 1` from `⟨p - 1, by have := hp.pos; omega⟩`.

Establish `hprod : ((n + 1 : ℕ) : 𝓞 E) ∈ l.Mb ^ n`. Establish `h1` using `hprim.prod_one_sub_pow_eq_order`. Rewrite using `[Nat.cast_succ, ← h1]`. Establish `: l.Mb ^ n = ∏ _k ∈ Finset.range n, l.Mb` using `by simp`. Rewrite using `[this]`.

Use `Ideal.prod_mem_prod fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← neg_sub]`. Conclude with `neg_mem (Ideal.mem_of_dvd _ (sub_one_dvd_pow_sub_one z _) hz1)`. Establish `hbar : ((n + 1 : ℕ) : 𝓞 E) ∈ (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ n`. Rewrite using `[← Ideal.map_pow]`.

Use `Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hprod` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hcop : IsCoprime (l.Mb ^ n) ((l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ n)` using `(Ideal.isCoprime_iff_sup_eq.2 l.coprime).pow`. Establish `h2 : ((n + 1 : ℕ) : 𝓞 E) ∈ Ideal.span {((l.M ^ n : ℕ) : 𝓞 E)}`. Rewrite using `[Nat.cast_pow, ← Ideal.span_singleton_pow, ← l.prod, mul_pow, Ideal.mul_eq_inf_of_isCoprime hcop]`.

Conclude with `⟨hprod, hbar⟩`. Establish `h4` using `hdiv _ _ (Ideal.mem_span_singleton.1 h2)`. Establish `h5` using `Nat.le_of_dvd hp.pos h4`. Establish `h6 : 3 ^ n ≤ l.M ^ n` using `Nat.pow_le_pow_left l.three_le n`. Establish `h7 : 1 ≤ n` using `by have := hp.two_le; omega`.

Establish `h8 : ∀ m : ℕ, 1 ≤ m → m + 1 < 3 ^ m` using `fun m hm => by`. Proceed by induction on `m, hm using Nat.le_induction with`. Consider the case `base => norm_num`. Consider the case `succ k _ ih => rw [pow_succ]`. Use linear arithmetic over natural numbers and integers.

Use `h8 n h7` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem eq_one_of_sub_mem (l : Level H) (d : 𝓞 E) (hd : ∀ ρ : E →+* ℂ, ‖ρ d‖ = 1) (hm : d - 1 ∈ l.Mb) : d = 1 := by
  obtain ⟨k, hk, hdk⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one E ℂ d.isIntegral_coe hd
  have hfin : IsOfFinOrder d := isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, by ext; simpa using hdk⟩
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (mt orderOf_eq_one_iff.1 hne)
  set z := d ^ (orderOf d / p) with hz
  have ho : orderOf z = p := orderOf_pow_orderOf_div hfin.orderOf_pos.ne' hpd
  have hz1 : z - 1 ∈ l.Mb := Ideal.mem_of_dvd _ (sub_one_dvd_pow_sub_one d _) hm
  have hprim : IsPrimitiveRoot z p := ho ▸ IsPrimitiveRoot.orderOf z
  have hn : ∀ a : ℕ, Algebra.norm ℤ (a : 𝓞 E) = (a : ℤ) ^ Module.finrank ℤ (𝓞 E) := fun a => by
    simpa using Algebra.norm_algebraMap (R := ℤ) (S := 𝓞 E) (a : ℤ)
  have hdiv : ∀ a b : ℕ, (a : 𝓞 E) ∣ b → a ∣ b := fun a b h => by
    have h3 := map_dvd (Algebra.norm ℤ) h
    rw [hn, hn, Int.pow_dvd_pow_iff Module.finrank_pos.ne'] at h3
    exact_mod_cast h3
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have hprod : ((n + 1 : ℕ) : 𝓞 E) ∈ l.Mb ^ n := by
    have h1 := hprim.prod_one_sub_pow_eq_order
    rw [Nat.cast_succ, ← h1]
    have : l.Mb ^ n = ∏ _k ∈ Finset.range n, l.Mb := by simp
    rw [this]
    refine Ideal.prod_mem_prod fun i _ => ?_
    rw [← neg_sub]
    exact neg_mem (Ideal.mem_of_dvd _ (sub_one_dvd_pow_sub_one z _) hz1)
  have hbar : ((n + 1 : ℕ) : 𝓞 E) ∈ (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ n := by
    rw [← Ideal.map_pow]
    have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hprod
    rwa [map_natCast] at this
  have hcop : IsCoprime (l.Mb ^ n) ((l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ n) :=
    (Ideal.isCoprime_iff_sup_eq.2 l.coprime).pow
  have h2 : ((n + 1 : ℕ) : 𝓞 E) ∈ Ideal.span {((l.M ^ n : ℕ) : 𝓞 E)} := by
    rw [Nat.cast_pow, ← Ideal.span_singleton_pow, ← l.prod, mul_pow, Ideal.mul_eq_inf_of_isCoprime hcop]
    exact ⟨hprod, hbar⟩
  have h4 := hdiv _ _ (Ideal.mem_span_singleton.1 h2)
  have h5 := Nat.le_of_dvd hp.pos h4
  have h6 : 3 ^ n ≤ l.M ^ n := Nat.pow_le_pow_left l.three_le n
  have h7 : 1 ≤ n := by have := hp.two_le; omega
  have h8 : ∀ m : ℕ, 1 ≤ m → m + 1 < 3 ^ m := fun m hm => by
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ k _ ih => rw [pow_succ]; omega
  have := h8 n h7
  omega

/- English proof (translation)
Take `⟨m, hgram, hper, hdet⟩` from `exists_matrix Di x hm hx gm hg`. Take `⟨hlin, h0, hR, hS⟩` from `hQ`. Establish `hP : ∀ ρ : E →+* ℂ, perMat x (Q.comp gm.toLinearMap.toAddMonoidHom) ρ = perMat x Q ρ * m.map (Formalism.L2.PjFree.relab c σ ρ)` using `fun ρ => by`. Use extensionality with `i k`. Conclude with `hper (Formalism.L2.PjFree.relab c σ ρ) ((Pi.evalAddMonoidHom (fun _ => ℂ) (⟨ρ, i⟩ : Pad.Letter Dw)).comp Q) (fun a v => hlin a v ⟨ρ, i⟩) k`.

Establish `hG : ∀ ρ : E →+* ℂ, (m.map ρ)ᵀ * hm.map ρ * m.map (conjEmb ρ) = hm.map ρ` using `fun ρ => by`. Establish `h1 : m.map (conjEmb ρ) = (m.map (IsCMField.complexConj E)).map ρ`. Use extensionality with `i j`. Conclude with `(IsCMField.complexEmbedding_complexConj E ρ _).symm`. Rewrite using `[h1, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hgram]`.

Establish `hdm : ∀ (ρ : E →+* ℂ) (u : Matrix (Idx Dw τ) (Idx Dw τ) E), (u.map ρ).det = ρ u.det` using `fun ρ u => (RingHom.map_det ρ u).symm`. Establish `hG0 : ∀ ρ : E →+* ℂ, (hm.map ρ).det ≠ 0` using `fun ρ => by`. Rewrite using `[hdm]`. Conclude with `(map_ne_zero ρ).2 hx.2.2.2`. Establish `hnorm : ∀ ρ : E →+* ℂ, ‖ρ m.det‖ = 1` using `fun ρ => by`.

Establish `h1` using `congrArg Matrix.det (hG ρ)`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_right_comm, mul_eq_right₀ (hG0 ρ), hdm, hdm]`. Establish `h2` using `congrArg norm h1`. Rewrite `h2` using `[norm_mul, norm_one, show conjEmb ρ m.det = starRingEnd ℂ (ρ m.det) from rfl, Complex.norm_conj]`. Use polynomial arithmetic with `[norm_nonneg (ρ m.det)]`.

Establish `hG1` using `hG (Formalism.L2.PjFree.relab c σ τ)`. Rewrite `hG1` using `[← GlobalTheory.UnifDataTest.relab_conj]`. Take `⟨hgood, hval⟩` from `HorIso.horVal_change (hG0 _) hG1 h0 hR hS`. Establish `hv : perVal c σ τ x hm (Q.comp gm.toLinearMap.toAddMonoidHom) = perVal c σ τ x hm Q * Formalism.L2.PjFree.relab c σ τ m.det`. Rewrite using `[perVal, kerMat, hP, hP, hval, hdm]`.

Both sides reduce to the same expression. Take `⟨d, hd, e⟩` from `hdet l.Mb (sub_mem_of_isLev l Di gm hlev)`. Rewrite using `[hv, e, eq_one_of_sub_mem l d (fun ρ => e ▸ hnorm ρ) hd]`. Simplify using the standard rewrite rules.
-/
theorem perVal_isLev {Dw : Datum H} {l : Level H} {c : Coeff l} {σ : c.F →+* ℂ} {Di : Datum H} {τ : E →+* ℂ}
    {x : Idx Dw τ → Di.La} {hm : Matrix (Idx Dw τ) (Idx Dw τ) E} {Q : Di.La →+ (Pad.Letter Dw → ℂ)}
    {gm : Di.La ≃ₗ[𝓞 E] Di.La} (hx : IsPerBasis Di x hm) (hQ : GoodPer c σ τ x hm Q) (hg : IsIsom Di gm)
    (hlev : IsLev l Di gm) :
    perVal c σ τ x hm (Q.comp gm.toLinearMap.toAddMonoidHom) = perVal c σ τ x hm Q := by
  obtain ⟨m, hgram, hper, hdet⟩ := exists_matrix Di x hm hx gm hg
  obtain ⟨hlin, h0, hR, hS⟩ := hQ
  have hP : ∀ ρ : E →+* ℂ, perMat x (Q.comp gm.toLinearMap.toAddMonoidHom) ρ =
      perMat x Q ρ * m.map (Formalism.L2.PjFree.relab c σ ρ) := fun ρ => by
    ext i k
    exact hper (Formalism.L2.PjFree.relab c σ ρ) ((Pi.evalAddMonoidHom (fun _ => ℂ) (⟨ρ, i⟩ : Pad.Letter Dw)).comp Q)
      (fun a v => hlin a v ⟨ρ, i⟩) k
  have hG : ∀ ρ : E →+* ℂ, (m.map ρ)ᵀ * hm.map ρ * m.map (conjEmb ρ) = hm.map ρ := fun ρ => by
    have h1 : m.map (conjEmb ρ) = (m.map (IsCMField.complexConj E)).map ρ := by
      ext i j
      exact (IsCMField.complexEmbedding_complexConj E ρ _).symm
    rw [h1, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hgram]
  have hdm : ∀ (ρ : E →+* ℂ) (u : Matrix (Idx Dw τ) (Idx Dw τ) E), (u.map ρ).det = ρ u.det := fun ρ u =>
    (RingHom.map_det ρ u).symm
  have hG0 : ∀ ρ : E →+* ℂ, (hm.map ρ).det ≠ 0 := fun ρ => by
    rw [hdm]; exact (map_ne_zero ρ).2 hx.2.2.2
  have hnorm : ∀ ρ : E →+* ℂ, ‖ρ m.det‖ = 1 := fun ρ => by
    have h1 := congrArg Matrix.det (hG ρ)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_right_comm, mul_eq_right₀ (hG0 ρ), hdm, hdm] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one, show conjEmb ρ m.det = starRingEnd ℂ (ρ m.det) from rfl, Complex.norm_conj] at h2
    nlinarith [norm_nonneg (ρ m.det)]
  have hG1 := hG (Formalism.L2.PjFree.relab c σ τ)
  rw [← GlobalTheory.UnifDataTest.relab_conj] at hG1
  obtain ⟨hgood, hval⟩ := HorIso.horVal_change (hG0 _) hG1 h0 hR hS
  have hv : perVal c σ τ x hm (Q.comp gm.toLinearMap.toAddMonoidHom) =
      perVal c σ τ x hm Q * Formalism.L2.PjFree.relab c σ τ m.det := by
    rw [perVal, kerMat, hP, hP, hval, hdm]; rfl
  obtain ⟨d, hd, e⟩ := hdet l.Mb (sub_mem_of_isLev l Di gm hlev)
  rw [hv, e, eq_one_of_sub_mem l d (fun ρ => e ▸ hnorm ρ) hd]
  simp

end Level

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Z hsm hsnc σ x₀`. Take `⟨a, e0, hx₀, he0, hhol, hsymm, hbd⟩` from `GlobalTheory.T.exists_snc_coordinates_complexPoint_smoothVariety c.F (gen Z) (genStr Z) Dw.dim (genBd Z) σ hsm hsnc x₀`. Establish `hsym0 : e0.symm 0 = x₀` using `by rw [← he0]; exact e0.left_inv hx₀`. Establish `h0t : (0 : Fin Dw.dim → ℂ) ∈ e0.target` using `he0 ▸ e0.map_source hx₀`. Take `⟨g, r₀, e, ex, ζ, h⟩` from `exists_framed_of_chart (a := a) e0 h0t hhol hsymm hbd`.

Rewrite `h` using `[hsym0]`. Conclude with `⟨Dw.dim, a, g, r₀, e, ex, ζ, h⟩`.
-/
theorem exists_framed_chart_snc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (hsm : SmoothOfRelativeDimension Dw.dim (genStr Z)) (hsnc : ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Z)) (σ : c.F →+* ℂ) (x₀ : CxPts (genStr Z) σ), ∃ (n a g r₀ : ℕ) (e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ), x₀ ∈ e.source ∧ e x₀ = 0 ∧ IsExpChart e ex ∧ (∀ x ∈ e.source, Inner x ↔ ∀ k : Fin n, (k : ℕ) < a → e x k ≠ 0) ∧ Function.Surjective (ex x₀) ∧ AnalyticOnNhd ℂ ζ (Metric.ball 0 1) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ex (e.symm z) (ζ z i) = 1) ∧ IsLatBasis {w | ex x₀ w = 1} (ζ 0) ∧ (∃ C : ℝ, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ‖ζ z‖ ≤ C) ∧ ∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1 := by
  intro E _ _ _ H Dw l Xo c O _ β Z hsm hsnc σ x₀
  obtain ⟨a, e0, hx₀, he0, hhol, hsymm, hbd⟩ :=
    GlobalTheory.T.exists_snc_coordinates_complexPoint_smoothVariety c.F (gen Z) (genStr Z) Dw.dim (genBd Z) σ hsm hsnc x₀
  have hsym0 : e0.symm 0 = x₀ := by rw [← he0]; exact e0.left_inv hx₀
  have h0t : (0 : Fin Dw.dim → ℂ) ∈ e0.target := he0 ▸ e0.map_source hx₀
  obtain ⟨g, r₀, e, ex, ζ, h⟩ := exists_framed_of_chart (a := a) e0 h0t hhol hsymm hbd
  rw [hsym0] at h
  exact ⟨Dw.dim, a, g, r₀, e, ex, ζ, h⟩

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Z hsm hsnc σ hσ hpq x₀`. Take `⟨n, a, g, r₀, e, ex, ζ, hx₀, he0, hEC, hbd, hsurj, hζan, hζli, hζK, hζB, hζC, hζstd⟩` from `exists_framed_chart_snc E H Dw l Xo c O β Z hsm hsnc σ x₀`. Take `⟨htarget, hholE, hsymmHol, hadd, hjoint, htan⟩` from `hEC`. Establish `hsymm : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, e.symm z ∈ e.source` using `fun z hz => e.map_target (by rw [htarget]; exact hz)`. Establish `hExpAt : ∀ x ∈ e.source, IsExpAt Z.t (x.1 ≫ genι Z) (ex x)` using `fun x hx => ⟨hadd x hx, (htan x hx).1, (htan x hx).2⟩`.

Establish `hzero : ∀ x ∈ e.source, ex x 0 = 1` using `fun x hx => by`. Use `hadd x hx 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `mul_eq_left.1 this.symm`. Establish `hHol : IsHolTo (Metric.ball (0 : Fin n → ℂ) 1 ×ˢ Set.univ) (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => (ex (e.symm zw.1) zw.2).left)` using `htarget ▸ hjoint`.

Establish `hslice : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, IsHolTo Set.univ (fun w => (ex (e.symm z) w).left)` using `fun z hz => by`. Use `GlobalTheory.HolPeriods.isHolTo_comp (φ := fun w : Fin g → ℂ => (z, w)) hHol isOpen_univ ((differentiableOn_const z).prodMk differentiableOn_id) fun w _ => Set.mk_mem_prod hz (Set.mem_univ w)` as an intermediate fact. Simplify using `only at this`. Conclude with `this`. Establish `h0 : e.symm 0 = x₀` using `by rw [← he0]; exact e.left_inv hx₀`.

Establish `hmem0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1` using `Metric.mem_ball_self one_pos`. Set `K : (Fin n → ℂ) → Set (Fin g → ℂ)` to `fun z => {w | ex (e.symm z) w = 1}`. Set `Pair : ℕ → (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℂˣ → Prop` to `fun N z v w c => GlobalTheory.UU.CubWeil Z.t.cub N (ex (e.symm z) ((N : ℂ)⁻¹ • v)) (ex (e.symm z) ((N : ℂ)⁻¹ • w)) (unitOn c)`. Establish `hLF : IsLatFam (Metric.ball 0 1) K` using `GlobalTheory.T.exponentialKernels_isHolomorphicLatticeFamily E H Z.X Z.t n g (Metric.ball 0 1) (fun z => (e.symm z).1 ≫ genι Z) (fun z => ex (e.symm z)) Metric.isOpen_ball hHol fun z hz => hExpAt _ (hsymm z hz)`. Establish `hB0 : IsLatBasis (K 0) (ζ 0)` using `by show IsLatBasis {w | ex (e.symm 0) w = 1} (ζ 0)`.

Rewrite using `[h0]`. Conclude with `hζB`. Establish `hP1 : ∀ N z v w c c', Pair N z v w c → Pair N z v w c' → c = c'` using `fun N z v w c c' h h' => unitOn_injective (h.unique h')`. Establish `hP2 : ∀ (m N : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ) (v w : (Fin m → ℂ) → Fin g → ℂ) (c : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → IsPreconnected B → DifferentiableOn ℂ φ B → Set.MapsTo φ B (Metric.ball 0 1) → DifferentiableOn ℂ v B → DifferentiableOn ℂ w B → …`. Introduce `m N B φ v w c b₀ b₁ hN hB hBc hφ hφm hv hw hK hb₀ hb₁ h`.

Establish `h1` using `GlobalTheory.HolPeriods.isHolTo_comp (φ := fun b => (φ b, (N : ℂ)⁻¹ • v b)) hHol hB (hφ.prodMk ((differentiableOn_const ((N : ℂ)⁻¹)).smul hv)) fun b hb => Set.mk_mem_prod (hφm hb) (Set.mem_univ _)`. Establish `h2` using `GlobalTheory.HolPeriods.isHolTo_comp (φ := fun b => (φ b, (N : ℂ)⁻¹ • w b)) hHol hB (hφ.prodMk ((differentiableOn_const ((N : ℂ)⁻¹)).smul hw)) fun b hb => Set.mk_mem_prod (hφm hb) (Set.mem_univ _)`. Simplify using `only at h1 h2`. Conclude with `GlobalTheory.T.cubicalWeilPairing_torsion_const_holomorphic_family Z.X Z.t.G Z.t.PP Z.t.cub m N B (fun b => (e.symm (φ b)).1 ≫ genι Z) (fun b => ex (e.symm (φ b)) ((N : ℂ)⁻¹ • v b)) (fun b => ex (e.symm (φ b)) ((N : ℂ)⁻¹ • w b)) c b₀ b₁ hN hB hBc h1 h2 (fun b hb => ⟨pow_eq_one_of …`. Establish `hP3 : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ Submodule.span ℝ (K z) = ⊤ ∧ (∀ v ∈ K z, ∀ w ∈ K z, ∃ m : ℤ, (hermForm Hm v w).im = m) ∧ ∀ (N …`.

Introduce `z hz hnz`. Establish `hin : Inner (e.symm z)` using `(hbd _ (hsymm z hz)).2 fun k hk => by`. Rewrite using `[e.right_inv (by rw [htarget]; exact hz)]`. Conclude with `hnz k hk`. Take `⟨Hm, hH, hpos, hspan, hint, hw⟩` from `GlobalTheory.T.exponentialKernel_lattice_riemannForm_off_boundary E H Dw l Xo c O β Z σ g (e.symm z) (ex (e.symm z)) hσ hpq hin (hExpAt _ (hsymm z hz)) (hslice z hz)`.

Conclude with `⟨Hm, hH, hpos, hspan, fun v hv w hw' => hint v w hv hw', fun N v w hN hv hw' => hw N v w _ hN hv hw' rfl⟩`. Establish `hP4 : ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ a a' : Fin r₀ → ℤ, (fun j => (a j : ZMod N)) ∈ S → Pair N 0 (∑ j, a j • ζ 0 j) (∑ j, a' j • ζ 0 j) 1`. Introduce `N hN`. Establish `hsl : IsHolTo Set.univ (fun w => (ex x₀ w).left)`. Use `hslice 0 hmem0` as an intermediate fact.

Rewrite `this` using `[h0]`. Conclude with `this`. Take `⟨Tt, hT1, hT2, hTc⟩` from `GlobalTheory.T.exists_toricTorsion_cubicalWeil_one_complexPoint E H Z.X Z.t (x₀.1 ≫ genι Z) g N (ex x₀) hN (hExpAt x₀ hx₀) hsurj hsl`. Take `⟨S, hSc, hS⟩` from `GlobalTheory.T.torsion_count_through_exponential_lattice_kernel _ g r₀ N (ex x₀) (ζ 0) Tt hN (hadd x₀ hx₀) hsurj hζB hT1 hTc`. Use `⟨S, hSc, fun a a' ha => ?_⟩` and prove the remaining obligations.

Use `show GlobalTheory.UU.CubWeil Z.t.cub N (ex (e.symm 0) ((N : ℂ)⁻¹ • ∑ j, a j • ζ 0 j)) (ex (e.symm 0) ((N : ℂ)⁻¹ • ∑ j, a' j • ζ 0 j)) (unitOn 1)`. Rewrite using `[h0, unitOn_one]`. Conclude with `hT2 _ (hS a ha) _ (pow_eq_one_of_map _ (hadd x₀ hx₀) (hzero x₀ hx₀) hN ((hζB.2 _).2 ⟨a', rfl⟩))`. Take `⟨r, lam, ρ, hc, hs, hg⟩` from `GlobalTheory.T.exists_holomorphic_latticeBasis_punctPolydiscCover_polyGrowth n a g r₀ K ζ Pair hLF hζan hζli hζK hB0 hζC hζstd hP1 hP2 hP3 hP4`. Conclude with `⟨n, g, r, a, e, ex, lam, ρ, hx₀, he0, ⟨htarget, hholE, hsymmHol, hadd, hjoint, htan⟩, hbd, hc, hs, hg⟩`.
-/
theorem exists_isLogChart_snc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (hsm : SmoothOfRelativeDimension Dw.dim (genStr Z)) (hsnc : ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Z)) (σ : c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb c σ → 1 ≤ Dw.p + Dw.q → ∀ x₀ : CxPts (genStr Z) σ, ∃ (n g r a : ℕ) (e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (ρ : Fin g → Fin r → ℂ), x₀ ∈ e.source ∧ e x₀ = 0 ∧ IsLogChart a e ex lam ρ := by
  intro E _ _ _ H Dw l Xo c O _ β Z hsm hsnc σ hσ hpq x₀
  obtain ⟨n, a, g, r₀, e, ex, ζ, hx₀, he0, hEC, hbd, hsurj, hζan, hζli, hζK, hζB, hζC, hζstd⟩ :=
    exists_framed_chart_snc E H Dw l Xo c O β Z hsm hsnc σ x₀
  obtain ⟨htarget, hholE, hsymmHol, hadd, hjoint, htan⟩ := hEC
  have hsymm : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, e.symm z ∈ e.source := fun z hz =>
    e.map_target (by rw [htarget]; exact hz)
  have hExpAt : ∀ x ∈ e.source, IsExpAt Z.t (x.1 ≫ genι Z) (ex x) := fun x hx =>
    ⟨hadd x hx, (htan x hx).1, (htan x hx).2⟩
  have hzero : ∀ x ∈ e.source, ex x 0 = 1 := fun x hx => by
    have := hadd x hx 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hHol : IsHolTo (Metric.ball (0 : Fin n → ℂ) 1 ×ˢ Set.univ)
      (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => (ex (e.symm zw.1) zw.2).left) := htarget ▸ hjoint
  have hslice : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, IsHolTo Set.univ (fun w => (ex (e.symm z) w).left) :=
    fun z hz => by
      have := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun w : Fin g → ℂ => (z, w)) hHol isOpen_univ
        ((differentiableOn_const z).prodMk differentiableOn_id) fun w _ => Set.mk_mem_prod hz (Set.mem_univ w)
      dsimp only at this
      exact this
  have h0 : e.symm 0 = x₀ := by rw [← he0]; exact e.left_inv hx₀
  have hmem0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  let K : (Fin n → ℂ) → Set (Fin g → ℂ) := fun z => {w | ex (e.symm z) w = 1}
  let Pair : ℕ → (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℂˣ → Prop := fun N z v w c =>
    GlobalTheory.UU.CubWeil Z.t.cub N (ex (e.symm z) ((N : ℂ)⁻¹ • v)) (ex (e.symm z) ((N : ℂ)⁻¹ • w)) (unitOn c)
  have hLF : IsLatFam (Metric.ball 0 1) K :=
    GlobalTheory.T.exponentialKernels_isHolomorphicLatticeFamily E H Z.X Z.t n g (Metric.ball 0 1) (fun z => (e.symm z).1 ≫ genι Z) (fun z => ex (e.symm z))
      Metric.isOpen_ball hHol fun z hz => hExpAt _ (hsymm z hz)
  have hB0 : IsLatBasis (K 0) (ζ 0) := by
    show IsLatBasis {w | ex (e.symm 0) w = 1} (ζ 0)
    rw [h0]
    exact hζB
  have hP1 : ∀ N z v w c c', Pair N z v w c → Pair N z v w c' → c = c' := fun N z v w c c' h h' =>
    unitOn_injective (h.unique h')
  have hP2 : ∀ (m N : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ) (v w : (Fin m → ℂ) → Fin g → ℂ)
      (c : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → IsPreconnected B → DifferentiableOn ℂ φ B →
      Set.MapsTo φ B (Metric.ball 0 1) → DifferentiableOn ℂ v B → DifferentiableOn ℂ w B →
      (∀ b ∈ B, v b ∈ K (φ b) ∧ w b ∈ K (φ b)) → b₀ ∈ B → b₁ ∈ B →
      Pair N (φ b₀) (v b₀) (w b₀) c → Pair N (φ b₁) (v b₁) (w b₁) c := by
    intro m N B φ v w c b₀ b₁ hN hB hBc hφ hφm hv hw hK hb₀ hb₁ h
    have h1 := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun b => (φ b, (N : ℂ)⁻¹ • v b)) hHol hB
      (hφ.prodMk ((differentiableOn_const ((N : ℂ)⁻¹)).smul hv)) fun b hb => Set.mk_mem_prod (hφm hb) (Set.mem_univ _)
    have h2 := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun b => (φ b, (N : ℂ)⁻¹ • w b)) hHol hB
      (hφ.prodMk ((differentiableOn_const ((N : ℂ)⁻¹)).smul hw)) fun b hb => Set.mk_mem_prod (hφm hb) (Set.mem_univ _)
    dsimp only at h1 h2
    exact GlobalTheory.T.cubicalWeilPairing_torsion_const_holomorphic_family Z.X Z.t.G Z.t.PP Z.t.cub m N B (fun b => (e.symm (φ b)).1 ≫ genι Z)
      (fun b => ex (e.symm (φ b)) ((N : ℂ)⁻¹ • v b)) (fun b => ex (e.symm (φ b)) ((N : ℂ)⁻¹ • w b)) c b₀ b₁ hN hB hBc
      h1 h2
      (fun b hb => ⟨pow_eq_one_of_map _ (hadd _ (hsymm _ (hφm hb))) (hzero _ (hsymm _ (hφm hb))) hN (hK b hb).1,
        pow_eq_one_of_map _ (hadd _ (hsymm _ (hφm hb))) (hzero _ (hsymm _ (hφm hb))) hN (hK b hb).2⟩) hb₀ hb₁ h
  have hP3 : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) →
      ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧
        Submodule.span ℝ (K z) = ⊤ ∧ (∀ v ∈ K z, ∀ w ∈ K z, ∃ m : ℤ, (hermForm Hm v w).im = m) ∧
        ∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K z → w ∈ K z →
          Pair N z v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N))
            (Complex.exp_ne_zero _)) := by
    intro z hz hnz
    have hin : Inner (e.symm z) := (hbd _ (hsymm z hz)).2 fun k hk => by
      rw [e.right_inv (by rw [htarget]; exact hz)]
      exact hnz k hk
    obtain ⟨Hm, hH, hpos, hspan, hint, hw⟩ := GlobalTheory.T.exponentialKernel_lattice_riemannForm_off_boundary E H Dw l Xo c O β Z σ g (e.symm z) (ex (e.symm z)) hσ hpq
      hin (hExpAt _ (hsymm z hz)) (hslice z hz)
    exact ⟨Hm, hH, hpos, hspan, fun v hv w hw' => hint v w hv hw', fun N v w hN hv hw' => hw N v w _ hN hv hw' rfl⟩
  have hP4 : ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧
      ∀ a a' : Fin r₀ → ℤ, (fun j => (a j : ZMod N)) ∈ S → Pair N 0 (∑ j, a j • ζ 0 j) (∑ j, a' j • ζ 0 j) 1 := by
    intro N hN
    have hsl : IsHolTo Set.univ (fun w => (ex x₀ w).left) := by
      have := hslice 0 hmem0
      rw [h0] at this
      exact this
    obtain ⟨Tt, hT1, hT2, hTc⟩ := GlobalTheory.T.exists_toricTorsion_cubicalWeil_one_complexPoint E H Z.X Z.t (x₀.1 ≫ genι Z) g N (ex x₀) hN (hExpAt x₀ hx₀) hsurj hsl
    obtain ⟨S, hSc, hS⟩ := GlobalTheory.T.torsion_count_through_exponential_lattice_kernel _ g r₀ N (ex x₀) (ζ 0) Tt hN (hadd x₀ hx₀) hsurj hζB hT1 hTc
    refine ⟨S, hSc, fun a a' ha => ?_⟩
    show GlobalTheory.UU.CubWeil Z.t.cub N (ex (e.symm 0) ((N : ℂ)⁻¹ • ∑ j, a j • ζ 0 j))
      (ex (e.symm 0) ((N : ℂ)⁻¹ • ∑ j, a' j • ζ 0 j)) (unitOn 1)
    rw [h0, unitOn_one]
    exact hT2 _ (hS a ha) _ (pow_eq_one_of_map _ (hadd x₀ hx₀) (hzero x₀ hx₀) hN ((hζB.2 _).2 ⟨a', rfl⟩))
  obtain ⟨r, lam, ρ, hc, hs, hg⟩ := GlobalTheory.T.exists_holomorphic_latticeBasis_punctPolydiscCover_polyGrowth n a g r₀ K ζ Pair hLF hζan hζli hζK hB0 hζC hζstd hP1 hP2 hP3 hP4
  exact ⟨n, g, r, a, e, ex, lam, ρ, hx₀, he0, ⟨htarget, hholE, hsymmHol, hadd, hjoint, htan⟩, hbd, hc, hs, hg⟩

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Z hsm hsnc σ g e Fu τ x hm h hσ hpq hx hh x₀`. Take `⟨n, g', r, k, ch, ex, lam, ρ, hx₀, hx₀', hch⟩` from `exists_isLogChart_snc E H Dw l Xo c O β Z hsm hsnc σ hσ hpq x₀`. Take `⟨i, T₀, hmark⟩` from `GlobalTheory.T.exists_constant_periodMarking_universalCover E H Dw l Xo c O β Z σ g e Fu n g' r k ch ex lam ρ hch`. Take `⟨C₂, k₂, hbnd⟩` from `GlobalTheory.T.horizontalCoordinate_polynomial_bound E H Dw l c σ (Fu.Di i) τ (x i) (hm i) g' r T₀ ρ (hx i)`. Take `⟨hexp, hinner, -, hlam, C₁, k₁, hgrow⟩` from `hch`.

Use `⟨ch.source ∩ ch ⁻¹' Metric.ball 0 (1 / 2), fun y => ∏ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), ch y j, ch.isOpen_inter_preimage Metric.isOpen_ball, ⟨hx₀, by simp [hx₀']⟩, ?_, fun y hy => ?_, ?_⟩` and prove the remaining obligations. Introduce `V _ _ _ B y hB hy hyN`. Conclude with `differentiableOn_finset_prod (f := fun j b => ch (y b) j) fun j _ => hexp.2.1 j V B y hB hy fun b hb => (hyN hb).1`. Rewrite using `[hinner y hy.1, Finset.prod_ne_zero_iff]`. Simplify using the standard rewrite rules.

Introduce `V _ _ _ B a hB ha haN b₀ hb₀`. Take `⟨W, Wi, hW, hWi, hdir⟩` from `GlobalTheory.T.exists_continuousOn_frameDirections_inverse E H Dw l Xo c O β Z σ n g' ch ex hexp V B a hB ha fun b hb => (haN b hb).1`. Establish `hBn : B ∈ 𝓝 b₀` using `hB.mem_nhds hb₀`. Take `⟨M, hM, hWM⟩` from `eventually_entries_le (hW.continuousAt hBn)`. Take `⟨M', hM', hWM'⟩` from `eventually_entries_le (hWi.continuousAt hBn)`.

Use `⟨C₂ * ((1 + M + M' + |C₁|) * 5 ^ k₁) ^ k₂, k₁ * k₂, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hBn, hWM, hWM'] with b hb hb1 hb2 hin`. Take `⟨hs1, hs2⟩` from `haN b hb`. Establish `hz : ‖ch (a b).1‖ < 1 / 2` using `by simpa using hs2`. Take `⟨s, hs, hse, hsi, hsn⟩` from `exists_log_lift k (ch (a b).1) hz ((hinner _ hs1).1 hin)`.

Take `⟨hd, hw1, hw2⟩` from `hdir b hb`. Take `⟨Q, gm, hQ, hgm, hv⟩` from `hmark s hs (a b) (W b) (by rw [hse, ch.left_inv hs1]) hd`. Establish `hgood` using `GlobalTheory.T.periodLinearAlgebra_hodgeSequence_exact E H Dw l Xo c O β Z σ g e Fu τ (a b) i Q (x i) (hm i) hQ (hx i)`. Take `⟨hgood', hnorm, -⟩` from `GlobalTheory.T.horizontalCoordinate_lattice_isometry_det_one E H Dw l c σ (Fu.Di i) τ (x i) (hm i) Q gm (hx i) hgood hgm`. Use `set L := 1 + |Real.log ‖∏ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), ch (a b).1 j‖| with hL`.

Establish `hL1 : 1 ≤ L` using `le_add_of_nonneg_right (abs_nonneg _)`. Establish `hP : 1 ≤ (5 * L) ^ k₁` using `one_le_pow₀ (by linarith)`. Establish `hC` using `abs_nonneg C₁`. Establish `hA : 1 + M + M' + |C₁| ≤ (1 + M + M' + |C₁|) * (5 * L) ^ k₁` using `le_mul_of_one_le_right (by positivity) hP`. Establish `hl : ‖lam s‖ ≤ (1 + M + M' + |C₁|) * (5 * L) ^ k₁`.

Combine the equalities or inequalities in the displayed calculation. Establish `key` using `hbnd (Q.comp gm.toLinearMap.toAddMonoidHom) (W b) (Wi b) (lam s) ((1 + M + M' + |C₁|) * (5 * L) ^ k₁) hgood' hw1 hw2 hv (hlam s hs).2.2 (by linarith) (fun z j => by linarith [hb1 z j]) (fun j z => by linarith [hb2 j z]) (fun m j => ((norm_le_pi_norm (lam s m) j).trans (norm_le_pi …`. Establish `heq : C₂ * ((1 + M + M' + |C₁|) * (5 * L) ^ k₁) ^ k₂ = C₂ * ((1 + M + M' + |C₁|) * 5 ^ k₁) ^ k₂ * L ^ (k₁ * k₂)`. Rewrite using `[mul_pow 5 L, ← _root_.mul_assoc, mul_pow _ (L ^ k₁), ← pow_mul, _root_.mul_assoc]`. Rewrite `key` using `[norm_inv, hnorm, heq]`.

Rewrite using `[hh (a b) i Q hQ, norm_inv]`. Conclude with `key`.
-/
theorem logGrowth_snc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (hsm : SmoothOfRelativeDimension Dw.dim (genStr Z)) (hsnc : ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Z)) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (τ : E →+* ℂ) (x : ∀ i, Idx Dw τ → (Fu.Di i).La) (hm : Fin Fu.n → Matrix (Idx Dw τ) (Idx Dw τ) E) (h : CxFr Z σ → ℂ), Formalism.L2.PjFree.GoodEmb c σ → 1 ≤ Dw.p + Dw.q → (∀ i, IsPerBasis (Fu.Di i) (x i) (hm i)) → (∀ a i Q, Per Fu a i Q → h a = perVal c σ τ (x i) (hm i) Q) → LogGrowth h := by
  intro E _ _ _ H Dw l Xo c O _ β Z hsm hsnc σ g e Fu τ x hm h hσ hpq hx hh x₀
  obtain ⟨n, g', r, k, ch, ex, lam, ρ, hx₀, hx₀', hch⟩ := exists_isLogChart_snc E H Dw l Xo c O β Z hsm hsnc σ hσ hpq x₀
  obtain ⟨i, T₀, hmark⟩ := GlobalTheory.T.exists_constant_periodMarking_universalCover E H Dw l Xo c O β Z σ g e Fu n g' r k ch ex lam ρ hch
  obtain ⟨C₂, k₂, hbnd⟩ := GlobalTheory.T.horizontalCoordinate_polynomial_bound E H Dw l c σ (Fu.Di i) τ (x i) (hm i) g' r T₀ ρ (hx i)
  obtain ⟨hexp, hinner, -, hlam, C₁, k₁, hgrow⟩ := hch
  refine ⟨ch.source ∩ ch ⁻¹' Metric.ball 0 (1 / 2),
    fun y => ∏ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), ch y j,
    ch.isOpen_inter_preimage Metric.isOpen_ball, ⟨hx₀, by simp [hx₀']⟩, ?_, fun y hy => ?_, ?_⟩
  · intro V _ _ _ B y hB hy hyN
    exact differentiableOn_finset_prod (f := fun j b => ch (y b) j) fun j _ =>
      hexp.2.1 j V B y hB hy fun b hb => (hyN hb).1
  · rw [hinner y hy.1, Finset.prod_ne_zero_iff]
    simp
  intro V _ _ _ B a hB ha haN b₀ hb₀
  obtain ⟨W, Wi, hW, hWi, hdir⟩ :=
    GlobalTheory.T.exists_continuousOn_frameDirections_inverse E H Dw l Xo c O β Z σ n g' ch ex hexp V B a hB ha fun b hb => (haN b hb).1
  have hBn : B ∈ 𝓝 b₀ := hB.mem_nhds hb₀
  obtain ⟨M, hM, hWM⟩ := eventually_entries_le (hW.continuousAt hBn)
  obtain ⟨M', hM', hWM'⟩ := eventually_entries_le (hWi.continuousAt hBn)
  refine ⟨C₂ * ((1 + M + M' + |C₁|) * 5 ^ k₁) ^ k₂, k₁ * k₂, ?_⟩
  filter_upwards [hBn, hWM, hWM'] with b hb hb1 hb2 hin
  obtain ⟨hs1, hs2⟩ := haN b hb
  have hz : ‖ch (a b).1‖ < 1 / 2 := by simpa using hs2
  obtain ⟨s, hs, hse, hsi, hsn⟩ := exists_log_lift k (ch (a b).1) hz ((hinner _ hs1).1 hin)
  obtain ⟨hd, hw1, hw2⟩ := hdir b hb
  obtain ⟨Q, gm, hQ, hgm, hv⟩ := hmark s hs (a b) (W b) (by rw [hse, ch.left_inv hs1]) hd
  have hgood := GlobalTheory.T.periodLinearAlgebra_hodgeSequence_exact E H Dw l Xo c O β Z σ g e Fu τ (a b) i Q (x i) (hm i) hQ (hx i)
  obtain ⟨hgood', hnorm, -⟩ := GlobalTheory.T.horizontalCoordinate_lattice_isometry_det_one E H Dw l c σ (Fu.Di i) τ (x i) (hm i) Q gm (hx i) hgood hgm
  set L := 1 + |Real.log ‖∏ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), ch (a b).1 j‖| with hL
  have hL1 : 1 ≤ L := le_add_of_nonneg_right (abs_nonneg _)
  have hP : 1 ≤ (5 * L) ^ k₁ := one_le_pow₀ (by linarith)
  have hC := abs_nonneg C₁
  have hA : 1 + M + M' + |C₁| ≤ (1 + M + M' + |C₁|) * (5 * L) ^ k₁ := le_mul_of_one_le_right (by positivity) hP
  have hl : ‖lam s‖ ≤ (1 + M + M' + |C₁|) * (5 * L) ^ k₁ :=
    calc ‖lam s‖ ≤ C₁ * (1 + ‖s‖) ^ k₁ := hgrow s hs (by rw [hse]; exact hz.le) hsi
      _ ≤ (1 + M + M' + |C₁|) * (5 * L) ^ k₁ :=
        mul_le_mul (by linarith [le_abs_self C₁]) (pow_le_pow_left₀ (by positivity) hsn _) (by positivity) (by positivity)
  have key := hbnd (Q.comp gm.toLinearMap.toAddMonoidHom) (W b) (Wi b) (lam s) ((1 + M + M' + |C₁|) * (5 * L) ^ k₁)
    hgood' hw1 hw2 hv (hlam s hs).2.2 (by linarith) (fun z j => by linarith [hb1 z j]) (fun j z => by linarith [hb2 j z])
    (fun m j => ((norm_le_pi_norm (lam s m) j).trans (norm_le_pi_norm (lam s) m)).trans hl)
  have heq : C₂ * ((1 + M + M' + |C₁|) * (5 * L) ^ k₁) ^ k₂ =
      C₂ * ((1 + M + M' + |C₁|) * 5 ^ k₁) ^ k₂ * L ^ (k₁ * k₂) := by
    rw [mul_pow 5 L, ← _root_.mul_assoc, mul_pow _ (L ^ k₁), ← pow_mul, _root_.mul_assoc]
  rw [norm_inv, hnorm, heq] at key
  rw [hh (a b) i Q hQ, norm_inv]
  exact key

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {σ : c.F →+* ℂ}
  {g : ℕ} {e : Fin g ≃ Pad.Letter Dw} {Fu : Fam Xo c σ e} {τ : E →+* ℂ} {x : ∀ i, Idx Dw τ → (Fu.Di i).La}
  {hm : Fin Fu.n → Matrix (Idx Dw τ) (Idx Dw τ) E}

/- English proof (translation)
Establish `hex : ∃ iQ : Σ i : Fin Fu.n, (Fu.Di i).La →+ (Letter Dw → ℂ), Per Fu a iQ.1 iQ.2` using `⟨⟨i, Q⟩, h⟩`. Rewrite using `[horOf, dif_pos hex]`. Establish `hs` using `hex.choose_spec`. Generalize the expression as in `hex.choose = w at hs`. Take `⟨j, Q'⟩` from `w`.

Apply the tactic sequence `obtain rfl : j = i := (GlobalTheory.T.two_markings_differ_by_level_isometry E H Dw l Xo c O β Z σ g e Fu a).1 _ _ _ _ hs h`. Apply the tactic sequence `obtain ⟨gm, h1, h2, h3⟩ := (GlobalTheory.T.two_markings_differ_by_level_isometry E H Dw l Xo c O β Z σ g e Fu a).2 _ _ _ h hs`. Use `perVal_isLev (hx j) (GlobalTheory.T.periodLinearAlgebra_hodgeSequence_exact E H Dw l Xo c O β Z σ g e Fu τ a j Q' _ _ hs (hx j)) h1 h2` as an intermediate fact. Rewrite using `[← this]`. Use `congr 1`.

Conclude with `AddMonoidHom.ext h3`.
-/
theorem horOf_eq_perVal {Z : Model Xo c β} (hx : ∀ i, IsPerBasis (Fu.Di i) (x i) (hm i))
    (a : CxFr Z σ) (i : Fin Fu.n) (Q : (Fu.Di i).La →+ (Letter Dw → ℂ)) (h : Per Fu a i Q) :
    horOf Fu τ x hm a = perVal c σ τ (x i) (hm i) Q := by
  have hex : ∃ iQ : Σ i : Fin Fu.n, (Fu.Di i).La →+ (Letter Dw → ℂ), Per Fu a iQ.1 iQ.2 := ⟨⟨i, Q⟩, h⟩
  rw [horOf, dif_pos hex]
  have hs := hex.choose_spec
  generalize hex.choose = w at hs
  obtain ⟨j, Q'⟩ := w
  obtain rfl : j = i := (GlobalTheory.T.two_markings_differ_by_level_isometry E H Dw l Xo c O β Z σ g e Fu a).1 _ _ _ _ hs h
  obtain ⟨gm, h1, h2, h3⟩ := (GlobalTheory.T.two_markings_differ_by_level_isometry E H Dw l Xo c O β Z σ g e Fu a).2 _ _ _ h hs
  have := perVal_isLev (hx j) (GlobalTheory.T.periodLinearAlgebra_hodgeSequence_exact E H Dw l Xo c O β Z σ g e Fu τ a j Q' _ _ hs (hx j)) h1 h2
  rw [← this]
  congr 1
  exact AddMonoidHom.ext h3

/- English proof (translation)
Establish `good` using `fun a i Q h => GlobalTheory.T.periodLinearAlgebra_hodgeSequence_exact E H Dw l Xo c O β Z σ g e Fu τ a i Q _ _ h (hx i)`. Use `⟨fun a ha => ?_, fun a a' M N ha hM hN => ?_, fun V _ _ _ B a hB hf hi b₀ hb => ?_, logGrowth_snc E H Dw l Xo c O β Z hsm hsnc σ g e Fu τ x hm _ hσ hr hx (horOf_eq_perVal hx)⟩` and prove the remaining obligations. Take `⟨i, Q, h⟩` from `GlobalTheory.T.exists_periods_in_frame_off_boundary E H Dw l Xo c O β Z σ g e Fu a ha`. Rewrite using `[horOf_eq_perVal hx a i Q h]`. Conclude with `(good a i Q h).perVal_ne_zero`.

Take `⟨i, Q, h⟩` from `GlobalTheory.T.exists_periods_in_frame_off_boundary E H Dw l Xo c O β Z σ g e Fu a ha`. Take `⟨Q', h', hc⟩` from `GlobalTheory.T.periods_change_of_eigenFrame E H Dw l Xo c O β Z σ g e Fu a a' i Q h hM.1`. Establish `key : ∀ ρ M, Chg a a' ρ M → perMat (x i) Q ρ = Mᵀ * perMat (x i) Q' ρ` using `fun ρ M hM => by`. Use extensionality with `j k`. Simplify using `only [perMat, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, hc ρ M hM, mul_comm]`.

Establish `k2 : kerMat c σ τ (x i) (hm i) Q = kerMat c σ τ (x i) (hm i) Q' * N`. Rewrite using `[kerMat, key _ _ hN, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc, kerMat]`. Take `⟨-, -, ⟨R, hR⟩, S, hS⟩` from `good a i Q h`. Take `⟨-, h0, -, S', hS'⟩` from `good a' i Q' h'`. Rewrite using `[horOf_eq_perVal hx a i Q h, horOf_eq_perVal hx a' i Q' h', perVal, perVal, k2, key _ _ hM]`.

Conclude with `GlobalTheory.ShFam.Hor.horVal_change N M h0 hS' (k2 ▸ hR) (key _ _ hM ▸ hS)`. Take `⟨B', i, Q, hB', hb', -, hP, hd⟩` from `GlobalTheory.T.exists_locally_holomorphic_periods_family E H Dw l Xo c O β Z σ g e Fu V B a hB hf hi b₀ hb`. Establish `hn` using `hB'.mem_nhds hb'`. Establish `hd' : ∀ v z, DifferentiableAt ℂ (fun b => Q b v z) b₀` using `fun v z => (hd v z).differentiableAt hn`. Take `⟨R, hR⟩` from `(good _ i _ (hP b₀ hb')).2.2.1`.

Use `DifferentiableAt.differentiableWithinAt (DifferentiableAt.congr_of_eventuallyEq (differentiableAt_horVal (K := fun b => kerMat c σ τ (x i) (hm i) (Q b)) (C := fun b => perMat (x i) (Q b) τ) (fun j k => ?_) (fun j k => hd' _ _) hR ?_) ?_)` and prove the remaining obligations. Simplify using `only [kerMat, Matrix.mul_apply]`. Conclude with `DifferentiableAt.fun_sum fun k _ => (differentiableAt_const _).mul (hd' _ _)`. Use `filter_upwards [hn] with b hb`. Conclude with `⟨(good _ i _ (hP b hb)).2.1, (good _ i _ (hP b hb)).2.2.2⟩`.

Use `filter_upwards [hn] with b hb`. Conclude with `horOf_eq_perVal hx _ i _ (hP b hb)`.
-/
theorem horFn_horOf_snc {Z : Model Xo c β} (hsm : SmoothOfRelativeDimension Dw.dim (genStr Z))
    (hsnc : ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Z)) (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hr : 1 ≤ Dw.p + Dw.q)
    (hx : ∀ i, IsPerBasis (Fu.Di i) (x i) (hm i)) :
    HorFn (Z := Z) τ (horOf Fu τ x hm) := by
  have good := fun a i Q h => GlobalTheory.T.periodLinearAlgebra_hodgeSequence_exact E H Dw l Xo c O β Z σ g e Fu τ a i Q _ _ h (hx i)
  refine ⟨fun a ha => ?_, fun a a' M N ha hM hN => ?_, fun V _ _ _ B a hB hf hi b₀ hb => ?_,
    logGrowth_snc E H Dw l Xo c O β Z hsm hsnc σ g e Fu τ x hm _ hσ hr hx (horOf_eq_perVal hx)⟩
  · obtain ⟨i, Q, h⟩ := GlobalTheory.T.exists_periods_in_frame_off_boundary E H Dw l Xo c O β Z σ g e Fu a ha
    rw [horOf_eq_perVal hx a i Q h]
    exact (good a i Q h).perVal_ne_zero
  · obtain ⟨i, Q, h⟩ := GlobalTheory.T.exists_periods_in_frame_off_boundary E H Dw l Xo c O β Z σ g e Fu a ha
    obtain ⟨Q', h', hc⟩ := GlobalTheory.T.periods_change_of_eigenFrame E H Dw l Xo c O β Z σ g e Fu a a' i Q h hM.1
    have key : ∀ ρ M, Chg a a' ρ M → perMat (x i) Q ρ = Mᵀ * perMat (x i) Q' ρ := fun ρ M hM => by
      ext j k
      simp only [perMat, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, hc ρ M hM, mul_comm]
    have k2 : kerMat c σ τ (x i) (hm i) Q = kerMat c σ τ (x i) (hm i) Q' * N := by
      rw [kerMat, key _ _ hN, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc, kerMat]
    obtain ⟨-, -, ⟨R, hR⟩, S, hS⟩ := good a i Q h
    obtain ⟨-, h0, -, S', hS'⟩ := good a' i Q' h'
    rw [horOf_eq_perVal hx a i Q h, horOf_eq_perVal hx a' i Q' h', perVal, perVal, k2, key _ _ hM]
    exact GlobalTheory.ShFam.Hor.horVal_change N M h0 hS' (k2 ▸ hR) (key _ _ hM ▸ hS)
  · obtain ⟨B', i, Q, hB', hb', -, hP, hd⟩ := GlobalTheory.T.exists_locally_holomorphic_periods_family E H Dw l Xo c O β Z σ g e Fu V B a hB hf hi b₀ hb
    have hn := hB'.mem_nhds hb'
    have hd' : ∀ v z, DifferentiableAt ℂ (fun b => Q b v z) b₀ := fun v z => (hd v z).differentiableAt hn
    obtain ⟨R, hR⟩ := (good _ i _ (hP b₀ hb')).2.2.1
    refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.congr_of_eventuallyEq
      (differentiableAt_horVal (K := fun b => kerMat c σ τ (x i) (hm i) (Q b)) (C := fun b => perMat (x i) (Q b) τ)
        (fun j k => ?_) (fun j k => hd' _ _) hR ?_) ?_)
    · simp only [kerMat, Matrix.mul_apply]
      exact DifferentiableAt.fun_sum fun k _ => (differentiableAt_const _).mul (hd' _ _)
    · filter_upwards [hn] with b hb
      exact ⟨(good _ i _ (hP b hb)).2.1, (good _ i _ (hP b hb)).2.2.2⟩
    · filter_upwards [hn] with b hb
      exact horOf_eq_perVal hx _ i _ (hP b hb)

end GlobalTheory.DetLine
