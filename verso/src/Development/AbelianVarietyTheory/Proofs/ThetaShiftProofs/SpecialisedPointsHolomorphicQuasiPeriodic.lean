import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyProjCoordsConvergentCoefficients
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFormalConvergence
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CoordsDetermineFamily
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsEvLePreimage
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LePreimageOfUnit

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.SpecHol

open Filter Topology GlobalTheory.Specialise GlobalTheory.HolHom GlobalTheory.CoordFamily

/- English proof (translation)
Introduce `O _ _ A lin cst hF`. Take `⟨T₀, h₀⟩` from `A.exists_isConvLine`. Use `⟨T₀, fun T hT j _ f hf w hw la v => ?_⟩` and prove the remaining obligations. Take `⟨n, r, α, th, h1, h2⟩` from `hf`. Establish `key : ∀ z, Conv.ev T w hw (f z) = ∑ i, Conv.ev T w hw ⟨r i, (h1 i).1⟩ * A.Sum j (α i) (th i) w z`.

Introduce `z`. Establish `hm : ∀ i, A.FSum j (α i) (th i) z ∈ Conv.halfRing T` using `fun i _ hw' => (AnArc.hasSum_coeff_FSum (h₀.mono hT) (h1 i).2 hw' z).summable`. Establish `hv : ∀ i, Conv.ev T w hw ⟨_, hm i⟩ = A.Sum j (α i) (th i) w z` using `fun i => Conv.ev_eq_of_hasSum hw _ (AnArc.hasSum_coeff_FSum (h₀.mono hT) (h1 i).2 hw z)`. Establish `e : f z = ∑ i, (⟨r i, (h1 i).1⟩ : Conv.halfRing T) * ⟨_, hm i⟩`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[AddSubmonoidClass.coe_finset_sum]`. Conclude with `h2 z`. Rewrite using `[e, map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [map_mul, hv i]`. Rewrite using `[key, key, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hF.sum w la v j (α i) (th i) (h1 i).2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ev_comb_factor : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), ∀ lin cst, IsFactor A lin cst → ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ (j : ℕ) [NeZero j] (f : A.V → Conv.halfRing T), IsComb A j (Conv.halfRing T) (fun v => f v) → ∀ w hw la v, Conv.ev T w hw (f (v + A.Pw w la)) = Complex.exp (lin w la v + cst w la) ^ j * Conv.ev T w hw (f v) := by
  intro O _ _ A lin cst hF
  obtain ⟨T₀, h₀⟩ := A.exists_isConvLine
  refine ⟨T₀, fun T hT j _ f hf w hw la v => ?_⟩
  obtain ⟨n, r, α, th, h1, h2⟩ := hf
  have key : ∀ z, Conv.ev T w hw (f z) =
      ∑ i, Conv.ev T w hw ⟨r i, (h1 i).1⟩ * A.Sum j (α i) (th i) w z := by
    intro z
    have hm : ∀ i, A.FSum j (α i) (th i) z ∈ Conv.halfRing T :=
      fun i _ hw' => (AnArc.hasSum_coeff_FSum (h₀.mono hT) (h1 i).2 hw' z).summable
    have hv : ∀ i, Conv.ev T w hw ⟨_, hm i⟩ = A.Sum j (α i) (th i) w z :=
      fun i => Conv.ev_eq_of_hasSum hw _ (AnArc.hasSum_coeff_FSum (h₀.mono hT) (h1 i).2 hw z)
    have e : f z = ∑ i, (⟨r i, (h1 i).1⟩ : Conv.halfRing T) * ⟨_, hm i⟩ := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finset_sum]
      exact h2 z
    rw [e, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hv i]
  rw [key, key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hF.sum w la v j (α i) (th i) (h1 i).2]
  ring

/- English proof (translation)
Take `⟨T₁, hT₁, hC, h₁⟩` from `SpecCoord.spec_coords E H D l B bb S s o A y Φ Γ Ψ N C`. Take `⟨T₂, h₂⟩` from `GlobalTheory.ArcPts.exists_formal_convergence _ A`. Take `⟨T₃, h₃⟩` from `ev_comb_factor _ A lin cst hF`. Use `set T := max T₁ (max T₂ T₃) with hT`. Establish `e₁ : T₁ ≤ T` using `le_max_left _ _`.

Establish `e₂ : T₂ ≤ T` using `(le_max_left _ _).trans (le_max_right _ _)`. Establish `e₃ : T₃ ≤ T` using `(le_max_right _ _).trans (le_max_right _ _)`. Use `⟨T, le_trans hT₁ e₁, fun w hw => ?_⟩` and prove the remaining obligations. Establish `hw₁ : T₁ < w.im` using `e₁.trans_lt hw`. Establish `hwC : C.T < w.im` using `hC.trans_lt hw₁`.

Establish `hwΨ : Ψ.T < w.im` using `lt_of_le_of_lt hT₁ hw₁`. Take `⟨hy, -, hval⟩` from `h₁ w hw₁`. Set `f : Fin C.n → A.V → Conv.halfRing T` to `fun i v => Subalgebra.inclusion (Conv.halfRing_mono (hC.trans e₁)) (C.cf i v)`. Establish `hf : ∀ i, IsComb A N (Conv.halfRing T) (fun v => f i v)` using `fun i => by`. Take `⟨n, r, α, th, h, h'⟩` from `C.comb i`.

Conclude with `⟨n, r, α, th, fun a => ⟨Conv.halfRing_mono (hC.trans e₁) (h a).1, (h a).2⟩, h'⟩`. Set `c : Fin C.n → A.V → ℂ` to `fun i v => Conv.ev C.T w hwC (C.cf i v)`. Establish `hcf : ∀ i v, c i v = Conv.ev T w hw (f i v)` using `fun i v => Conv.ev_congr hwC hw rfl`. Establish `hd : ∀ i, Differentiable ℂ (c i)` using `fun i => by`. Rewrite using `[show c i = fun v => Conv.ev T w hw (f i v) from funext (hcf i)]`.

Conclude with `(h₂ T e₂ N).2 (f i) (hf i) w hw`. Establish `hp : ∀ la v i, c i (v + A.Pw w la) = Complex.exp (lin w la v + cst w la) ^ N * c i v` using `fun la v i => by`. Rewrite using `[hcf, hcf]`. Conclude with `h₃ T e₃ N (f i) (hf i) w hw la v`. Establish `hfr` using `(SpecGroup.specPts_group E H D l B bb S s o A y Φ Γ Ψ w hwΨ).2.2.1`.

Establish `hex : ∀ v, ∃ x : Sp ℂ ⟶ (o.t.G.hom ⁻¹ᵁ C.U).toScheme, x ≫ (o.t.G.hom ⁻¹ᵁ C.U).ι = (Ψ.pi w v).left` using `fun v => by`. Establish `hxU : ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ (o.t.G.hom ⁻¹ᵁ C.U)`. Rewrite using `[← Scheme.Hom.comp_preimage, Over.w]`. Conclude with `hy`. Conclude with `⟨IsOpenImmersion.lift (o.t.G.hom ⁻¹ᵁ C.U).ι (Ψ.pi w v).left (by`.

Introduce and unpack `_ ⟨p, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `hxU (x := p) trivial), IsOpenImmersion.lift_fac _ _ _⟩`. Use `choose x hx using hex`. Establish `hv : ∀ i v j, ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j → valR (x v) ((Out.powOver o.t.G o.t.PP.L C.U N).U (fun _ => j)) ((C.b i).f (fun _ => j)) = c i v * Ψ.fr w j v ^ N` using `fun i v j hj => hval i v (x v) j (hx v) hj`.

Establish `hc : ∀ v, HasCoords (x v) C.b fun i => c i v` using `fun v => hasCoords_powOver o.t.PP.isLB fun j hj => by`. Rewrite `hj` using `[hx]`. Conclude with `⟨((hfr v).1 j hj).unit ^ N, fun i => by simpa using hv i v j hj⟩`. Establish `hi : (o.t.G.hom ∣_ C.U) ≫ C.U.ι = (o.t.G.hom ⁻¹ᵁ C.U).ι ≫ o.t.G.hom` using `morphismRestrict_ι _ _`. Establish `hy' : ∀ v, x v ≫ (o.t.G.hom ∣_ C.U) = x 0 ≫ (o.t.G.hom ∣_ C.U)` using `fun v => by`.

Rewrite using `[← cancel_mono C.U.ι, Category.assoc, Category.assoc, hi, ← Category.assoc, ← Category.assoc, hx, hx, Over.w, Over.w]`. Establish `hhol : ∀ z, HolAt x z` using `fun z => holAt_of_coords C.emb hy' hc fun i => hd i z`. Establish `hhol' : ∀ z, HolAt (fun v => (Ψ.pi w v).left) z` using `fun z => by`. Use `(hhol z).comp (o.t.G.hom ⁻¹ᵁ C.U).ι` as an intermediate fact. Simplify `this` using `only [hx]`.

Establish `hper : ∀ la v, x v = x (v + A.Pw w la)` using `fun la v => eq_of_proportional C.emb ((hy' _).trans (hy' _).symm) (hc v) (hc _) (hp la v)`. Establish `hper' : ∀ la v, Ψ.pi w (v + A.Pw w la) = Ψ.pi w v` using `fun la v => Over.OverMorphism.ext (by rw [← hx, ← hx, ← hper])`. Use `⟨hhol', hper', fun j z hj => ?_, fun la v j hj => ?_⟩` and prove the remaining obligations. Take `⟨i, hi0⟩` from `C.bpf w hwC z`. Establish `hzj : ⊤ ≤ x z ⁻¹ᵁ (Out.powOver o.t.G o.t.PP.L C.U N).U (fun _ => j)`.

Introduce `p _`. Rewrite `hj` using `[← hx]`. Conclude with `Set.mem_iInter.2 fun _ => hj (x := p) trivial`. Establish `h1` using `(hhol z _ hzj).2 ((C.b i).f (fun _ => j))`. Establish `hne : ∀ᶠ v in 𝓝 z, c i v ≠ 0` using `(hd i z).continuousAt.eventually_ne hi0`.

Use `(h1.fun_mul ((hd i z).fun_inv hi0)).congr_of_eventuallyEq (((hhol' z _ hj).1.and hne).mono fun v hv' => ?_)` and prove the remaining obligations. Simplify using `only [valAt'_eq_valR]`. Rewrite using `[hv i v j hv'.1, mul_comm, inv_mul_cancel_left₀ hv'.2]`. Take `⟨i, hi0⟩` from `C.bpf w hwC v`. Establish `h1` using `hv i v j hj`.

Establish `h2` using `hv i (v + A.Pw w la) j (by rw [hper']; exact hj)`. Rewrite `h2` using `[← hper, h1, hp]`. Apply `mul_left_cancel₀ (show c i v ≠ 0 from hi0)` to reduce the goal to its premises. Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem of_coords (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H)
    (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B)
    (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ)
    (lin : ℂ → A.La → A.V →ₗ[ℂ] ℂ) (cst : ℂ → A.La → ℂ) (hF : IsFactor A lin cst) (N : ℕ) [NeZero N]
    (C : Coords Φ N) :
    ∃ T' ≥ Ψ.T, ∀ w : ℂ, T' < w.im → (∀ z, HolAt (fun v => (Ψ.pi w v).left) z) ∧
      (∀ la v, Ψ.pi w (v + A.Pw w la) = Ψ.pi w v) ∧
      (∀ j z, ⊤ ≤ (Ψ.pi w z).left ⁻¹ᵁ o.t.PP.L.U j → DifferentiableAt ℂ (fun v => Ψ.fr w j v ^ N) z) ∧
      ∀ la v j, ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j →
        Ψ.fr w j v ^ N = (Complex.exp (lin w la v + cst w la) * Ψ.fr w j (v + A.Pw w la)) ^ N := by
  obtain ⟨T₁, hT₁, hC, h₁⟩ := SpecCoord.spec_coords E H D l B bb S s o A y Φ Γ Ψ N C
  obtain ⟨T₂, h₂⟩ := GlobalTheory.ArcPts.exists_formal_convergence _ A
  obtain ⟨T₃, h₃⟩ := ev_comb_factor _ A lin cst hF
  set T := max T₁ (max T₂ T₃) with hT
  have e₁ : T₁ ≤ T := le_max_left _ _
  have e₂ : T₂ ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have e₃ : T₃ ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨T, le_trans hT₁ e₁, fun w hw => ?_⟩
  have hw₁ : T₁ < w.im := e₁.trans_lt hw
  have hwC : C.T < w.im := hC.trans_lt hw₁
  have hwΨ : Ψ.T < w.im := lt_of_le_of_lt hT₁ hw₁
  obtain ⟨hy, -, hval⟩ := h₁ w hw₁
  let f : Fin C.n → A.V → Conv.halfRing T := fun i v => Subalgebra.inclusion (Conv.halfRing_mono (hC.trans e₁)) (C.cf i v)
  have hf : ∀ i, IsComb A N (Conv.halfRing T) (fun v => f i v) := fun i => by
    obtain ⟨n, r, α, th, h, h'⟩ := C.comb i
    exact ⟨n, r, α, th, fun a => ⟨Conv.halfRing_mono (hC.trans e₁) (h a).1, (h a).2⟩, h'⟩
  let c : Fin C.n → A.V → ℂ := fun i v => Conv.ev C.T w hwC (C.cf i v)
  have hcf : ∀ i v, c i v = Conv.ev T w hw (f i v) := fun i v => Conv.ev_congr hwC hw rfl
  have hd : ∀ i, Differentiable ℂ (c i) := fun i => by
    rw [show c i = fun v => Conv.ev T w hw (f i v) from funext (hcf i)]
    exact (h₂ T e₂ N).2 (f i) (hf i) w hw
  have hp : ∀ la v i, c i (v + A.Pw w la) = Complex.exp (lin w la v + cst w la) ^ N * c i v := fun la v i => by
    rw [hcf, hcf]
    exact h₃ T e₃ N (f i) (hf i) w hw la v
  have hfr := (SpecGroup.specPts_group E H D l B bb S s o A y Φ Γ Ψ w hwΨ).2.2.1
  have hex : ∀ v, ∃ x : Sp ℂ ⟶ (o.t.G.hom ⁻¹ᵁ C.U).toScheme, x ≫ (o.t.G.hom ⁻¹ᵁ C.U).ι = (Ψ.pi w v).left := fun v => by
    have hxU : ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ (o.t.G.hom ⁻¹ᵁ C.U) := by
      rw [← Scheme.Hom.comp_preimage, Over.w]
      exact hy
    exact ⟨IsOpenImmersion.lift (o.t.G.hom ⁻¹ᵁ C.U).ι (Ψ.pi w v).left (by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hxU (x := p) trivial), IsOpenImmersion.lift_fac _ _ _⟩
  choose x hx using hex
  have hv : ∀ i v j, ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j →
      valR (x v) ((Out.powOver o.t.G o.t.PP.L C.U N).U (fun _ => j)) ((C.b i).f (fun _ => j)) =
        c i v * Ψ.fr w j v ^ N := fun i v j hj => hval i v (x v) j (hx v) hj
  have hc : ∀ v, HasCoords (x v) C.b fun i => c i v := fun v => hasCoords_powOver o.t.PP.isLB fun j hj => by
    rw [hx] at hj
    exact ⟨((hfr v).1 j hj).unit ^ N, fun i => by simpa using hv i v j hj⟩
  have hi : (o.t.G.hom ∣_ C.U) ≫ C.U.ι = (o.t.G.hom ⁻¹ᵁ C.U).ι ≫ o.t.G.hom := morphismRestrict_ι _ _
  have hy' : ∀ v, x v ≫ (o.t.G.hom ∣_ C.U) = x 0 ≫ (o.t.G.hom ∣_ C.U) := fun v => by
    rw [← cancel_mono C.U.ι, Category.assoc, Category.assoc, hi, ← Category.assoc, ← Category.assoc, hx, hx,
      Over.w, Over.w]
  have hhol : ∀ z, HolAt x z := fun z => holAt_of_coords C.emb hy' hc fun i => hd i z
  have hhol' : ∀ z, HolAt (fun v => (Ψ.pi w v).left) z := fun z => by
    have := (hhol z).comp (o.t.G.hom ⁻¹ᵁ C.U).ι
    simpa only [hx] using this
  have hper : ∀ la v, x v = x (v + A.Pw w la) := fun la v =>
    eq_of_proportional C.emb ((hy' _).trans (hy' _).symm) (hc v) (hc _) (hp la v)
  have hper' : ∀ la v, Ψ.pi w (v + A.Pw w la) = Ψ.pi w v := fun la v =>
    Over.OverMorphism.ext (by rw [← hx, ← hx, ← hper])
  refine ⟨hhol', hper', fun j z hj => ?_, fun la v j hj => ?_⟩
  · obtain ⟨i, hi0⟩ := C.bpf w hwC z
    have hzj : ⊤ ≤ x z ⁻¹ᵁ (Out.powOver o.t.G o.t.PP.L C.U N).U (fun _ => j) := by
      intro p _
      rw [← hx] at hj
      exact Set.mem_iInter.2 fun _ => hj (x := p) trivial
    have h1 := (hhol z _ hzj).2 ((C.b i).f (fun _ => j))
    have hne : ∀ᶠ v in 𝓝 z, c i v ≠ 0 := (hd i z).continuousAt.eventually_ne hi0
    refine (h1.fun_mul ((hd i z).fun_inv hi0)).congr_of_eventuallyEq
      (((hhol' z _ hj).1.and hne).mono fun v hv' => ?_)
    simp only [valAt'_eq_valR]
    rw [hv i v j hv'.1, mul_comm, inv_mul_cancel_left₀ hv'.2]
  · obtain ⟨i, hi0⟩ := C.bpf w hwC v
    have h1 := hv i v j hj
    have h2 := hv i (v + A.Pw w la) j (by rw [hper']; exact hj)
    rw [← hper, h1, hp] at h2
    apply mul_left_cancel₀ (show c i v ≠ 0 from hi0)
    rw [h2]
    ring

/- English proof (translation)
Introduce `hL hL2 E _ _ _ H _ D l B _ bb S _ s o A y Φ Γ Ψ hA hΦ lin cst hF`. Take `⟨C₄⟩` from `GlobalTheory.SpanFrame.nonempty_coords hL hL2 E H D l B bb S s o A y Φ hA hΦ 4 le_rfl`. Take `⟨C₅⟩` from `GlobalTheory.SpanFrame.nonempty_coords hL hL2 E H D l B bb S s o A y Φ hA hΦ 5 (by norm_num)`. Take `⟨T₄, hT₄, h₄⟩` from `of_coords E H D l B bb S s o A y Φ Γ Ψ lin cst hF 4 C₄`. Take `⟨T₅, -, h₅⟩` from `of_coords E H D l B bb S s o A y Φ Γ Ψ lin cst hF 5 C₅`.

Use `⟨max T₄ T₅, le_max_of_le_left hT₄, fun w hw => ?_⟩` and prove the remaining obligations. Establish `hw₄ : T₄ < w.im` using `(le_max_left _ _).trans_lt hw`. Take `⟨hhol, hper, hd₄, hq₄⟩` from `h₄ w hw₄`. Take `⟨-, -, hd₅, hq₅⟩` from `h₅ w ((le_max_right _ _).trans_lt hw)`. Take `⟨hadd, -, hfr, -⟩` from `SpecGroup.specPts_group E H D l B bb S s o A y Φ Γ Ψ w (lt_of_le_of_lt hT₄ hw₄)`.

Establish `hne : ∀ v j, ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j → Ψ.fr w j v ≠ 0` using `fun v j hj => ((hfr v).1 j hj).ne_zero`. Use `⟨isHolTo_of_holAt isOpen_univ fun z _ => hhol z, fun la => ?_, fun j z hz => ?_, fun la v j hj => ?_⟩` and prove the remaining obligations. Establish `h` using `hper la 0`. Rewrite `h` using `[hadd]`. Conclude with `mul_eq_left.1 h`.

Use `DifferentiableAt.differentiableWithinAt ?_` and prove the remaining obligations. Use `((hd₅ j z hz).fun_mul ((hd₄ j z hz).fun_inv (pow_ne_zero _ (hne z j hz)))).congr_of_eventuallyEq ((hhol z _ hz).1.mono fun v hv => ?_)` and prove the remaining obligations. Use `hne v j hv` as an intermediate fact. Use `beta_reduce`. Clear the denominators using the available nonvanishing facts.

Establish `h` using `hq₅ la v j hj`. Rewrite `h` using `[pow_succ _ 4, pow_succ _ 4, ← hq₄ la v j hj]`. Conclude with `mul_left_cancel₀ (pow_ne_zero _ (hne v j hj)) h`.
-/
theorem specPts_holomorphic : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), AnFin A → Φ.Rational → ∀ lin cst, IsFactor A lin cst → ∃ T' ≥ Ψ.T, ∀ w : ℂ, T' < w.im → IsHolTo Set.univ (fun v => (Ψ.pi w v).left) ∧ (∀ la, Ψ.pi w (A.Pw w la) = 1) ∧ (∀ j, DifferentiableOn ℂ (Ψ.fr w j) {v | ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j}) ∧ ∀ la v j, ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j → Ψ.fr w j v = Complex.exp (lin w la v + cst w la) * Ψ.fr w j (v + A.Pw w la) := by
  intro hL hL2 E _ _ _ H _ D l B _ bb S _ s o A y Φ Γ Ψ hA hΦ lin cst hF
  obtain ⟨C₄⟩ := GlobalTheory.SpanFrame.nonempty_coords hL hL2 E H D l B bb S s o A y Φ hA hΦ 4 le_rfl
  obtain ⟨C₅⟩ := GlobalTheory.SpanFrame.nonempty_coords hL hL2 E H D l B bb S s o A y Φ hA hΦ 5 (by norm_num)
  obtain ⟨T₄, hT₄, h₄⟩ := of_coords E H D l B bb S s o A y Φ Γ Ψ lin cst hF 4 C₄
  obtain ⟨T₅, -, h₅⟩ := of_coords E H D l B bb S s o A y Φ Γ Ψ lin cst hF 5 C₅
  refine ⟨max T₄ T₅, le_max_of_le_left hT₄, fun w hw => ?_⟩
  have hw₄ : T₄ < w.im := (le_max_left _ _).trans_lt hw
  obtain ⟨hhol, hper, hd₄, hq₄⟩ := h₄ w hw₄
  obtain ⟨-, -, hd₅, hq₅⟩ := h₅ w ((le_max_right _ _).trans_lt hw)
  obtain ⟨hadd, -, hfr, -⟩ := SpecGroup.specPts_group E H D l B bb S s o A y Φ Γ Ψ w (lt_of_le_of_lt hT₄ hw₄)
  have hne : ∀ v j, ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j → Ψ.fr w j v ≠ 0 := fun v j hj => ((hfr v).1 j hj).ne_zero
  refine ⟨isHolTo_of_holAt isOpen_univ fun z _ => hhol z, fun la => ?_, fun j z hz => ?_, fun la v j hj => ?_⟩
  · have h := hper la 0
    rw [hadd] at h
    exact mul_eq_left.1 h
  · refine DifferentiableAt.differentiableWithinAt ?_
    refine ((hd₅ j z hz).fun_mul ((hd₄ j z hz).fun_inv (pow_ne_zero _ (hne z j hz)))).congr_of_eventuallyEq
      ((hhol z _ hz).1.mono fun v hv => ?_)
    have := hne v j hv
    beta_reduce
    field_simp
  · have h := hq₅ la v j hj
    rw [pow_succ _ 4, pow_succ _ 4, ← hq₄ la v j hj] at h
    exact mul_left_cancel₀ (pow_ne_zero _ (hne v j hj)) h

end GlobalTheory.SpecHol
