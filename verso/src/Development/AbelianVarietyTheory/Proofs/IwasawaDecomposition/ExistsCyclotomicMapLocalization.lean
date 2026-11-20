import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory

namespace GlobalTheory.SiegLoc

/- English proof (translation)
Take `⟨k, rfl⟩` from `h`. Establish `ha : (a : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (left_ne_zero_of_mul hm)`. Establish `hk : (k : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (right_ne_zero_of_mul hm)`. Establish `: zeta a = zeta (a * k) ^ k`. Unfold `zeta`.

Rewrite using `[← Complex.exp_nat_mul]`. Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`.

Conclude with `pow_mem hz k`.
-/
theorem zeta_mem_coeff_of_dvd {F : IntermediateField ℚ ℂ} {a m : ℕ} (hm : m ≠ 0) (h : a ∣ m) (hz : zeta m ∈ F) :
    zeta a ∈ F := by
  obtain ⟨k, rfl⟩ := h
  have ha : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (left_ne_zero_of_mul hm)
  have hk : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (right_ne_zero_of_mul hm)
  have : zeta a = zeta (a * k) ^ k := by
    unfold zeta
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  rw [this]
  exact pow_mem hz k

/- English proof (translation)
Introduce `E _ _ _ H l c n R _ b ω hn hd hω hb hloc`. Use `letI : Algebra (𝓞 c.F) R := b.toAlgebra`. Use `haveI := c.fin`. Use `haveI : NumberField c.F := {}`. Establish `hn0 : n ≠ 0` using `by omega`.

Establish `hinj : Function.Injective ω`. Use `letI : Algebra R c.F := ω.toAlgebra`. Use `haveI := hω.2.2`. Conclude with `IsFractionRing.injective R c.F`. Set `f : R →+* ℂ` to `(c.F.val.toRingHom).comp ω`.

Establish `hf : Function.Injective f` using `Subtype.val_injective.comp hinj`. Establish `hfb : ∀ x : 𝓞 c.F, f (b x) = ((x : c.F) : ℂ)` using `fun x => by`. Use `RingHom.congr_fun hb x` as an intermediate fact. Simplify using `only [RingHom.comp_apply] at this`. Use `show ((ω (b x) : c.F) : ℂ) = _`.

Rewrite using `[this]`. Establish `hM' : l.M' ≠ 0` using `Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'`. Establish `hz : zeta n ∈ c.F` using `zeta_mem_coeff_of_dvd hM' (hd.trans (Nat.dvd_lcm_left _ _)) c.zeta_mem`. Establish `hzi : IsIntegral ℤ (⟨zeta n, hz⟩ : c.F)`. Establish `h1 : IsPrimitiveRoot (⟨zeta n, hz⟩ : c.F) n` using `IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom) (Complex.isPrimitiveRoot_exp n hn0) Subtype.val_injective`.

Conclude with `h1.isIntegral (Nat.pos_of_ne_zero hn0)`. Take `⟨u, hu⟩ : IsUnit (algebraMap (𝓞 c.F) R (n : 𝓞 c.F))` from `IsLocalization.Away.algebraMap_isUnit _`. Rewrite `hu` using `[map_natCast]`. Establish `hfu : f ((u⁻¹ : Rˣ) : R) = (n : ℂ)⁻¹`. Apply `eq_inv_of_mul_eq_one_right` to reduce the goal to its premises.

Rewrite using `[← map_natCast f n, ← hu, ← map_mul, Units.mul_inv, map_one]`. Establish `hle : cycAway n ≤ f.range`. Unfold `cycAway`. Rewrite using `[Subring.closure_le]`. Introduce and unpack `x (rfl | rfl)`.

Conclude with `⟨b ⟨_, hzi⟩, hfb _⟩`. Conclude with `⟨_, hfu⟩`. Set `e : R ≃+* f.range` to `RingEquiv.ofBijective f.rangeRestrict ⟨fun x y h => hf (show f x = f y from congrArg (fun t : f.range => (t : ℂ)) h), f.rangeRestrict_surjective⟩`. Set `κ : cycAway n →+* R` to `e.symm.toRingHom.comp (Subring.inclusion hle)`. Establish `hκ : ∀ x, f (κ x) = (x : ℂ)` using `fun x => congrArg Subtype.val (e.apply_symm_apply (Subring.inclusion hle x))`.

Use `⟨κ, hκ, ?_⟩` and prove the remaining obligations. Use `letI : Algebra (cycAway n) R := κ.toAlgebra`. Set `v : cycAway n` to `⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩`. Establish `hv : κ v = ((u⁻¹ : Rˣ) : R)` using `hf (by rw [hκ, hfu])`. Take `⟨S, hS⟩ : (⊤ : Submodule ℤ (𝓞 c.F)).FG` from `Module.Finite.fg_top`.

Use `⟨⟨S.image b, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Establish `hbx : ∀ x : 𝓞 c.F, b x ∈ Submodule.span (cycAway n) ((S.image b : Finset R) : Set R)`. Introduce `x`. Establish `hx : x ∈ Submodule.span ℤ (S : Set (𝓞 c.F))` using `hS ▸ Submodule.mem_top`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact Submodule.subset_span (by rw [Finset.coe_image]; exact ⟨y, hy, rfl⟩)`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz => rw [map_add]`.

Conclude with `add_mem hy hz`. Consider the case `smul a y _ hy => rw [map_zsmul]`. Conclude with `zsmul_mem hy a`. Introduce `r _`. Take `⟨k, x, hx⟩` from `IsLocalization.Away.surj (S := R) (n : 𝓞 c.F) r`.

Rewrite `hx` using `[map_natCast, ← hu]`. Establish `hr : r = (v ^ k) • b x` using `by show r = κ (v ^ k) * b x`. Establish `hx' : r * (u : R) ^ k = b x` using `hx`. Rewrite using `[map_pow, hv, ← hx', mul_left_comm, ← mul_pow, Units.inv_mul, one_pow, mul_one]`. Rewrite using `[hr]`.

Conclude with `Submodule.smul_mem _ _ (hbx x)`.
-/
theorem exists_cycAway_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (n : ℕ) (R : Type) [CommRing R] (b : 𝓞 c.F →+* R) (ω : R →+* c.F), 3 ≤ n → n ∣ l.M → IsDedFrac ω → ω.comp b = algebraMap (𝓞 c.F) c.F → @IsLocalization.Away (𝓞 c.F) _ (n : 𝓞 c.F) R _ b.toAlgebra → ∃ κ : cycAway n →+* R, (∀ x, ((ω (κ x) : c.F) : ℂ) = (x : ℂ)) ∧ κ.Finite := by
  intro E _ _ _ H l c n R _ b ω hn hd hω hb hloc
  letI : Algebra (𝓞 c.F) R := b.toAlgebra
  haveI := c.fin
  haveI : NumberField c.F := {}
  have hn0 : n ≠ 0 := by omega
  have hinj : Function.Injective ω := by
    letI : Algebra R c.F := ω.toAlgebra
    haveI := hω.2.2
    exact IsFractionRing.injective R c.F
  let f : R →+* ℂ := (c.F.val.toRingHom).comp ω
  have hf : Function.Injective f := Subtype.val_injective.comp hinj
  have hfb : ∀ x : 𝓞 c.F, f (b x) = ((x : c.F) : ℂ) := fun x => by
    have := RingHom.congr_fun hb x
    simp only [RingHom.comp_apply] at this
    show ((ω (b x) : c.F) : ℂ) = _
    rw [this]
  have hM' : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  have hz : zeta n ∈ c.F := zeta_mem_coeff_of_dvd hM' (hd.trans (Nat.dvd_lcm_left _ _)) c.zeta_mem
  have hzi : IsIntegral ℤ (⟨zeta n, hz⟩ : c.F) := by
    have h1 : IsPrimitiveRoot (⟨zeta n, hz⟩ : c.F) n :=
      IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom)
        (Complex.isPrimitiveRoot_exp n hn0) Subtype.val_injective
    exact h1.isIntegral (Nat.pos_of_ne_zero hn0)
  obtain ⟨u, hu⟩ : IsUnit (algebraMap (𝓞 c.F) R (n : 𝓞 c.F)) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_natCast] at hu
  have hfu : f ((u⁻¹ : Rˣ) : R) = (n : ℂ)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← map_natCast f n, ← hu, ← map_mul, Units.mul_inv, map_one]
  have hle : cycAway n ≤ f.range := by
    unfold cycAway
    rw [Subring.closure_le]
    rintro x (rfl | rfl)
    · exact ⟨b ⟨_, hzi⟩, hfb _⟩
    · exact ⟨_, hfu⟩
  let e : R ≃+* f.range := RingEquiv.ofBijective f.rangeRestrict
    ⟨fun x y h => hf (show f x = f y from congrArg (fun t : f.range => (t : ℂ)) h), f.rangeRestrict_surjective⟩
  let κ : cycAway n →+* R := e.symm.toRingHom.comp (Subring.inclusion hle)
  have hκ : ∀ x, f (κ x) = (x : ℂ) := fun x =>
    congrArg Subtype.val (e.apply_symm_apply (Subring.inclusion hle x))
  refine ⟨κ, hκ, ?_⟩
  letI : Algebra (cycAway n) R := κ.toAlgebra
  let v : cycAway n := ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩
  have hv : κ v = ((u⁻¹ : Rˣ) : R) := hf (by rw [hκ, hfu])
  obtain ⟨S, hS⟩ : (⊤ : Submodule ℤ (𝓞 c.F)).FG := Module.Finite.fg_top
  classical
  refine ⟨⟨S.image b, ?_⟩⟩
  rw [eq_top_iff]
  have hbx : ∀ x : 𝓞 c.F, b x ∈ Submodule.span (cycAway n) ((S.image b : Finset R) : Set R) := by
    intro x
    have hx : x ∈ Submodule.span ℤ (S : Set (𝓞 c.F)) := hS ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (by rw [Finset.coe_image]; exact ⟨y, hy, rfl⟩)
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul a y _ hy => rw [map_zsmul]; exact zsmul_mem hy a
  intro r _
  obtain ⟨k, x, hx⟩ := IsLocalization.Away.surj (S := R) (n : 𝓞 c.F) r
  rw [map_natCast, ← hu] at hx
  have hr : r = (v ^ k) • b x := by
    show r = κ (v ^ k) * b x
    have hx' : r * (u : R) ^ k = b x := hx
    rw [map_pow, hv, ← hx', mul_left_comm, ← mul_pow, Units.inv_mul, one_pow, mul_one]
  rw [hr]
  exact Submodule.smul_mem _ _ (hbx x)

end GlobalTheory.SiegLoc
