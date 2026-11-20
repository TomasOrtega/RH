import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.CintIdx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.MemCOfInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.LatCls

noncomputable section

namespace UpperTheory.V.Z.Sym.Loc.PK

open QuadraticAlgebra Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ τ : K}

variable (O) in

structure Gen1 (x : Etau K τ) : Prop where
  tr : QuadraticAlgebra.trace x ∈ (algebraMap O K).range
  nm : QuadraticAlgebra.norm x ∈ (algebraMap O K).range
  disc : ∃ u : Oˣ, algebraMap O K u = x.im ^ 2 * (τ ^ 2 - 4)

/- English proof (translation)
Use `haveI := L.frac`. Conclude with `IsIntegrallyClosed.algebraMap_eq_of_integral (IsIntegral.of_pow (n := 2) (by norm_num) (h ▸ isIntegral_algebraMap))`.
-/
theorem sq_int (L : IsLoc O Δ) (x : K) (a : O) (h : x ^ 2 = algebraMap O K a) : ∃ b : O, algebraMap O K b = x := by
  haveI := L.frac
  exact IsIntegrallyClosed.algebraMap_eq_of_integral (IsIntegral.of_pow (n := 2) (by norm_num) (h ▸ isIntegral_algebraMap))

/- English proof (translation)
Use `haveI := L.frac`. Conclude with `IsIntegrallyClosed.algebraMap_eq_of_integral ((isIntegral_algebraMap_iff (algebraMap K (Etau K τ)).injective).1 h)`.
-/
theorem int_down (L : IsLoc O Δ) (a : K) (h : IsIntegral O (algebraMap K (Etau K τ) a)) : ∃ b : O, algebraMap O K b = a := by
  haveI := L.frac
  exact IsIntegrallyClosed.algebraMap_eq_of_integral ((isIntegral_algebraMap_iff (algebraMap K (Etau K τ)).injective).1 h)

omit [IsDomain O] [IsDiscreteValuationRing O] in
/- English proof (translation)
Take `⟨t, ht⟩` from `h.tr`. Take `⟨n, hn⟩` from `h.nm`. Conclude with `isIntegral_of_trace_norm t n ht.symm hn.symm`.
-/
theorem Gen1.int {x : Etau K τ} (h : Gen1 O x) : IsIntegral O x := by
  obtain ⟨t, ht⟩ := h.tr
  obtain ⟨n, hn⟩ := h.nm
  exact isIntegral_of_trace_norm t n ht.symm hn.symm

omit [IsDomain O] [IsDiscreteValuationRing O] in
/- English proof (translation)
Introduce `h0` and use `by obtain ⟨u, hu⟩ := h.disc exact (u.isUnit.map (algebraMap O K)).ne_zero (by rw [hu, h0]; ring)`.
-/
theorem Gen1.im_ne [Nontrivial O] {x : Etau K τ} (h : Gen1 O x) : x.im ≠ 0 := fun h0 => by
  obtain ⟨u, hu⟩ := h.disc
  exact (u.isUnit.map (algebraMap O K)).ne_zero (by rw [hu, h0]; ring)

/- English proof (translation)
Use `⟨fun hy => ?_, ?_⟩` and prove the remaining obligations. Establish `h0` using `h.im_ne`. Take `⟨u, hu⟩` from `h.disc`. Take `⟨d, hd⟩` from `int_down L (y.im ^ 2 * (τ ^ 2 - 4)) (by`. Use `(hy.sub (isIntegral_star hy)).pow 2 using 1` and compare the differences between its conclusion and the goal.

Apply the tactic sequence `ext <;> simp [sq] <;> ring)`. Establish `hi : algebraMap O K u * algebraMap O K (u⁻¹ : Oˣ) = 1` using `by rw [← map_mul, Units.mul_inv, map_one]`. Take `⟨b, hb⟩` from `sq_int L (y.im / x.im) (d * (u⁻¹ : Oˣ)) (by`. Rewrite using `[map_mul, hd]`. Rewrite `hi` using `[hu]`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `(-y.im ^ 2) * hi)`. Take `⟨a, ha⟩` from `int_down (τ := τ) L (y.re - y.im / x.im * x.re) (by`. Use `hy.sub ((isIntegral_algebraMap (x := b)).mul h.int) using 1` and compare the differences between its conclusion and the goal. Rewrite using `[algebraMap_etau (O := O), hb]`.

Apply the tactic sequence `ext <;> simp`. Clear the denominators using the available nonvanishing facts. Use the proof step `ring)`. Use `⟨a, b, ?_⟩` and prove the remaining obligations. Rewrite using `[algebraMap_etau a, algebraMap_etau b, ha, hb]`.

Apply the tactic sequence `ext <;> simp`. Clear the denominators using the available nonvanishing facts. Introduce and unpack `⟨a, b, rfl⟩`. Conclude with `isIntegral_algebraMap.add (isIntegral_algebraMap.mul h.int)`.
-/
theorem Gen1.int_iff (L : IsLoc O Δ) {x : Etau K τ} (h : Gen1 O x) (y : Etau K τ) :
    IsIntegral O y ↔ ∃ a b : O, y = algebraMap O _ a + algebraMap O _ b * x := by
  refine ⟨fun hy => ?_, ?_⟩
  · have h0 := h.im_ne
    obtain ⟨u, hu⟩ := h.disc
    obtain ⟨d, hd⟩ := int_down L (y.im ^ 2 * (τ ^ 2 - 4)) (by
      convert (hy.sub (isIntegral_star hy)).pow 2 using 1
      ext <;> simp [sq] <;> ring)
    have hi : algebraMap O K u * algebraMap O K (u⁻¹ : Oˣ) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    obtain ⟨b, hb⟩ := sq_int L (y.im / x.im) (d * (u⁻¹ : Oˣ)) (by
      rw [map_mul, hd]; rw [hu] at hi; field_simp; linear_combination (-y.im ^ 2) * hi)
    obtain ⟨a, ha⟩ := int_down (τ := τ) L (y.re - y.im / x.im * x.re) (by
      convert hy.sub ((isIntegral_algebraMap (x := b)).mul h.int) using 1
      rw [algebraMap_etau (O := O), hb]
      ext <;> simp
      field_simp; ring)
    refine ⟨a, b, ?_⟩
    rw [algebraMap_etau a, algebraMap_etau b, ha, hb]
    ext <;> simp
    field_simp
  · rintro ⟨a, b, rfl⟩
    exact isIntegral_algebraMap.add (isIntegral_algebraMap.mul h.int)

/- English proof (translation)
Use `haveI := L.frac`. Take `⟨y, x', h0, ⟨t, ht⟩, ⟨n, hn⟩, rfl⟩` from `latCls O K Δ τ L hτ S hS`. Establish `hi : IsIntegral O x'` using `isIntegral_of_trace_norm t n ht.symm hn.symm`. Take `⟨_, hw, e⟩` from `hx _ ⟨1, Submodule.subset_span (by simp), rfl⟩`. Take `⟨p, q, rfl⟩` from `Submodule.mem_span_pair.1 hw`.

Establish `e' : p • (1 : Etau K τ) + q • x' = x`. Use `(Units.mul_right_inj y).1 ?_` and prove the remaining obligations. Simplify `e` using `[mul_comm]`. Use `⟨y, fun w => ⟨?_, fun hw => ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨_, hw, rfl⟩`.

Take `⟨a, b, rfl⟩` from `Submodule.mem_span_pair.1 hw`. Rewrite using `[Units.inv_mul_cancel_left]`. Conclude with `(isIntegral_one.smul a).add (hi.smul b)`. Take `⟨a, b, e⟩` from `(h.int_iff L _).1 hw`. Use `⟨_, Submodule.mem_span_pair.2 ⟨a + b * p, b * q, rfl⟩, ?_⟩` and prove the remaining obligations.

Establish `: (a + b * p) • (1 : Etau K τ) + (b * q) • x' = ((y⁻¹ : (Etau K τ)ˣ) : Etau K τ) * w`. Rewrite using `[e, ← e']`. Simplify using `only [Algebra.smul_def, map_add, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Express the relevant statement in the definitionally equal form `(y : Etau K τ) * _ = w`.

Rewrite using `[this, Units.mul_inv_cancel_left]`.
-/
theorem Gen1.princ (L : IsLoc O Δ) (hτ : τ ^ 2 - 4 ≠ 0) {x : Etau K τ} (h : Gen1 O x) {S : Set (Etau K τ)} (hS : IsLat O τ S) (hx : ∀ w ∈ S, x * w ∈ S) :
    ∃ u : (Etau K τ)ˣ, ∀ w, w ∈ S ↔ IsIntegral O (((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) * w) := by
  haveI := L.frac
  obtain ⟨y, x', h0, ⟨t, ht⟩, ⟨n, hn⟩, rfl⟩ := latCls O K Δ τ L hτ S hS
  have hi : IsIntegral O x' := isIntegral_of_trace_norm t n ht.symm hn.symm
  obtain ⟨_, hw, e⟩ := hx _ ⟨1, Submodule.subset_span (by simp), rfl⟩
  obtain ⟨p, q, rfl⟩ := Submodule.mem_span_pair.1 hw
  have e' : p • (1 : Etau K τ) + q • x' = x := by
    refine (Units.mul_right_inj y).1 ?_
    simpa [mul_comm] using e
  refine ⟨y, fun w => ⟨?_, fun hw => ?_⟩⟩
  · rintro ⟨_, hw, rfl⟩
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hw
    rw [Units.inv_mul_cancel_left]
    exact (isIntegral_one.smul a).add (hi.smul b)
  · obtain ⟨a, b, e⟩ := (h.int_iff L _).1 hw
    refine ⟨_, Submodule.mem_span_pair.2 ⟨a + b * p, b * q, rfl⟩, ?_⟩
    have : (a + b * p) • (1 : Etau K τ) + (b * q) • x' = ((y⁻¹ : (Etau K τ)ˣ) : Etau K τ) * w := by
      rw [e, ← e']; simp only [Algebra.smul_def, map_add, map_mul]; ring
    change (y : Etau K τ) * _ = w
    rw [this, Units.mul_inv_cancel_left]

/- English proof (translation)
Use `haveI := L.frac`. Establish `h0` using `h.im_ne`. Establish `key : ∀ (s : K) (a b : O), (IsUnit a ∨ IsUnit b) → (c : Etau K τ) = algebraMap K _ s * (algebraMap O _ a + algebraMap O _ b * x) → ∃ (s : Kˣ) (u : (Etau K τ)ˣ), IsIntegral O (u : Etau K τ) ∧ IsIntegral O ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) ∧ c = PS.sc τ s * u`. Introduce `s a b hab e`. Establish `hs : s ≠ 0` using `fun h => c.ne_zero (by rw [e, h]; simp)`.

Set `u : (Etau K τ)ˣ` to `(PS.sc τ (Units.mk0 s hs))⁻¹ * c`. Establish `hu : (u : Etau K τ) = algebraMap O _ a + algebraMap O _ b * x`. Rewrite using `[Units.val_mul, e]`. Conclude with `Units.inv_mul_cancel_left (PS.sc τ (Units.mk0 s hs)) _`. Establish `huc : u ∈ Cint O τ` using `mul_mem (inv_mem (PS.sc_mem _)) hc`.

Establish `h1 : IsIntegral O (((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) * star (u : Etau K τ))` using `by simpa [quo] using huc.2`. Take `⟨d, hd⟩` from `h.disc`. Establish `hxx : (x - star x) ^ 2 = algebraMap O _ (d : O)`. Apply the tactic sequence `rw [algebraMap_etau (O := O), hd]; ext <;> simp [sq] <;> ring`. Establish `hsu : star (u : Etau K τ) = algebraMap O _ a + algebraMap O _ b * star x`.

Apply the tactic sequence `rw [hu, algebraMap_etau a, algebraMap_etau b]; ext <;> simp <;> ring`. Establish `hui` using `u.inv_mul`. Use `set i := ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ)`. Establish `hdi : algebraMap O (Etau K τ) (d : O) * algebraMap O _ ((d⁻¹ : Oˣ) : O) = 1` using `by rw [← map_mul, Units.mul_inv, map_one]`. Establish `h2 : IsIntegral O (i * algebraMap O _ b)`.

Use `((isIntegral_one.sub h1).mul (h.int.sub (isIntegral_star h.int))).mul (isIntegral_algebraMap (x := ((d⁻¹ : Oˣ) : O))) using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hsu]`. Rewrite `hui` using `[hu]`. Take the linear combination `(-(i * algebraMap O _ b)) * hdi - (i * algebraMap O _ b * algebraMap O _ ((d⁻¹ : Oˣ) : O)) * hxx + ((x - star x) * algebraMap O _ ((d⁻¹ : Oˣ) : O)) * hui`. Establish `h3 : IsIntegral O (i * algebraMap O _ a)`.

Use `isIntegral_one.sub (h2.mul h.int) using 1` and compare the differences between its conclusion and the goal. Rewrite `hui` using `[hu]`. Take the linear combination `hui`. Establish `h4 : ∀ e : O, IsUnit e → IsIntegral O (i * algebraMap O _ e) → IsIntegral O i` using `fun e he hi => by`. Take `⟨f, hf⟩` from `he.exists_right_inv`.

Use `hi.mul (isIntegral_algebraMap (x := f))` as an intermediate fact. Rewrite `this` using `[mul_assoc, ← map_mul, hf, map_one, mul_one]`. Then use the resulting hypothesis. Conclude with `⟨Units.mk0 s hs, u, hu ▸ isIntegral_algebraMap.add (isIntegral_algebraMap.mul h.int), hab.elim (h4 a · h3) (h4 b · h2), by simp [u]⟩`. Apply the tactic sequence `obtain ⟨α, β, e⟩ : ∃ α β : K, (c : Etau K τ) = algebraMap K _ α + algebraMap K _ β * x := ⟨(c : Etau K τ).re - (c : Etau K τ).im / x.im * x.re, (c : Etau K τ).im / x.im, by ext <;> simp; field_simp⟩`. Distinguish the cases in `hβ : β = 0`.

Conclude with `key α 1 0 (.inl isUnit_one) (by simp [e, hβ])`. Break down `ValuationRing.isInteger_or_isInteger O (α / β) with ⟨r, hr⟩ | ⟨r, hr⟩` into its components or cases. Use `key β r 1 (.inr isUnit_one) ?_` and prove the remaining obligations. Rewrite using `[e, algebraMap_etau (O := O), hr, map_one, one_mul, mul_add, ← map_mul, mul_div_cancel₀ _ hβ]`. Distinguish the cases in `hα : α = 0`.

Conclude with `key β 0 1 (.inr isUnit_one) (by simp [e, hα])`. Use `key α 1 r (.inl isUnit_one) ?_` and prove the remaining obligations. Rewrite using `[e, algebraMap_etau r, hr, map_one, mul_add, mul_one, ← mul_assoc, ← map_mul, inv_div, mul_div_cancel₀ _ hα]`.
-/
theorem Gen1.cint (L : IsLoc O Δ) {x : Etau K τ} (h : Gen1 O x) {c : (Etau K τ)ˣ} (hc : c ∈ Cint O τ) :
    ∃ (s : Kˣ) (u : (Etau K τ)ˣ), IsIntegral O (u : Etau K τ) ∧ IsIntegral O ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) ∧ c = PS.sc τ s * u := by
  haveI := L.frac
  have h0 := h.im_ne
  have key : ∀ (s : K) (a b : O), (IsUnit a ∨ IsUnit b) → (c : Etau K τ) = algebraMap K _ s * (algebraMap O _ a + algebraMap O _ b * x) →
      ∃ (s : Kˣ) (u : (Etau K τ)ˣ), IsIntegral O (u : Etau K τ) ∧ IsIntegral O ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) ∧ c = PS.sc τ s * u := by
    intro s a b hab e
    have hs : s ≠ 0 := fun h => c.ne_zero (by rw [e, h]; simp)
    let u : (Etau K τ)ˣ := (PS.sc τ (Units.mk0 s hs))⁻¹ * c
    have hu : (u : Etau K τ) = algebraMap O _ a + algebraMap O _ b * x := by
      rw [Units.val_mul, e]; exact Units.inv_mul_cancel_left (PS.sc τ (Units.mk0 s hs)) _
    have huc : u ∈ Cint O τ := mul_mem (inv_mem (PS.sc_mem _)) hc
    have h1 : IsIntegral O (((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) * star (u : Etau K τ)) := by simpa [quo] using huc.2
    obtain ⟨d, hd⟩ := h.disc
    have hxx : (x - star x) ^ 2 = algebraMap O _ (d : O) := by
      rw [algebraMap_etau (O := O), hd]; ext <;> simp [sq] <;> ring
    have hsu : star (u : Etau K τ) = algebraMap O _ a + algebraMap O _ b * star x := by
      rw [hu, algebraMap_etau a, algebraMap_etau b]; ext <;> simp <;> ring
    have hui := u.inv_mul
    set i := ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ)
    have hdi : algebraMap O (Etau K τ) (d : O) * algebraMap O _ ((d⁻¹ : Oˣ) : O) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have h2 : IsIntegral O (i * algebraMap O _ b) := by
      convert ((isIntegral_one.sub h1).mul (h.int.sub (isIntegral_star h.int))).mul (isIntegral_algebraMap (x := ((d⁻¹ : Oˣ) : O))) using 1
      rw [hsu]; rw [hu] at hui
      linear_combination (-(i * algebraMap O _ b)) * hdi - (i * algebraMap O _ b * algebraMap O _ ((d⁻¹ : Oˣ) : O)) * hxx +
        ((x - star x) * algebraMap O _ ((d⁻¹ : Oˣ) : O)) * hui
    have h3 : IsIntegral O (i * algebraMap O _ a) := by
      convert isIntegral_one.sub (h2.mul h.int) using 1
      rw [hu] at hui
      linear_combination hui
    have h4 : ∀ e : O, IsUnit e → IsIntegral O (i * algebraMap O _ e) → IsIntegral O i := fun e he hi => by
      obtain ⟨f, hf⟩ := he.exists_right_inv
      have := hi.mul (isIntegral_algebraMap (x := f))
      rwa [mul_assoc, ← map_mul, hf, map_one, mul_one] at this
    exact ⟨Units.mk0 s hs, u, hu ▸ isIntegral_algebraMap.add (isIntegral_algebraMap.mul h.int), hab.elim (h4 a · h3) (h4 b · h2), by simp [u]⟩
  obtain ⟨α, β, e⟩ : ∃ α β : K, (c : Etau K τ) = algebraMap K _ α + algebraMap K _ β * x :=
    ⟨(c : Etau K τ).re - (c : Etau K τ).im / x.im * x.re, (c : Etau K τ).im / x.im, by ext <;> simp; field_simp⟩
  by_cases hβ : β = 0
  · exact key α 1 0 (.inl isUnit_one) (by simp [e, hβ])
  rcases ValuationRing.isInteger_or_isInteger O (α / β) with ⟨r, hr⟩ | ⟨r, hr⟩
  · refine key β r 1 (.inr isUnit_one) ?_
    rw [e, algebraMap_etau (O := O), hr, map_one, one_mul, mul_add, ← map_mul, mul_div_cancel₀ _ hβ]
  · by_cases hα : α = 0
    · exact key β 0 1 (.inr isUnit_one) (by simp [e, hα])
    refine key α 1 r (.inl isUnit_one) ?_
    rw [e, algebraMap_etau r, hr, map_one, mul_add, mul_one, ← mul_assoc, ← map_mul, inv_div, mul_div_cancel₀ _ hα]

variable (O τ) in

def Mx : Set (Etau K τ) := {w | IsIntegral O w}

omit [IsDomain O] [IsDiscreteValuationRing O] in
/- English proof (translation)
Use extensionality with `w`. Rewrite using `[PS.mem_ml]`. Conclude with `⟨fun hw => show IsIntegral O w by simpa using h.mul hw, fun hw => h'.mul hw⟩`.
-/
theorem ml_Mx {u : (Etau K τ)ˣ} (h : IsIntegral O (u : Etau K τ)) (h' : IsIntegral O ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ)) : PS.ml u (Mx O τ) = Mx O τ := by
  ext w
  rw [PS.mem_ml]
  exact ⟨fun hw => show IsIntegral O w by simpa using h.mul hw, fun hw => h'.mul hw⟩

/- English proof (translation)
Use extensionality with `w`. Rewrite using `[SetLike.mem_coe, Submodule.mem_span_pair, Mx, Set.mem_setOf_eq, h.int_iff L]`. Simplify using `only [Algebra.smul_def, mul_one, eq_comm]`.
-/
theorem Gen1.span (L : IsLoc O Δ) {x : Etau K τ} (h : Gen1 O x) : Mx O τ = (Submodule.span O {1, x} : Submodule O (Etau K τ)) := by
  ext w
  rw [SetLike.mem_coe, Submodule.mem_span_pair, Mx, Set.mem_setOf_eq, h.int_iff L]
  simp only [Algebra.smul_def, mul_one, eq_comm]

/- English proof (translation)
Use `⟨⟨{1, x}, by rw [h.span L]; simp⟩, eq_top_iff.2 fun w _ => ?_⟩` and prove the remaining obligations. Establish `h0` using `h.im_ne`. Rewrite using `[show w = (w.re - w.im / x.im * x.re) • (1 : Etau K τ) + (w.im / x.im) • x by`. Apply the tactic sequence `ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]; field_simp]`. Conclude with `add_mem (Submodule.smul_mem _ _ (Submodule.subset_span isIntegral_one)) (Submodule.smul_mem _ _ (Submodule.subset_span h.int))`.
-/
theorem Gen1.lat (L : IsLoc O Δ) {x : Etau K τ} (h : Gen1 O x) : IsLat O τ (Mx O τ) := by
  classical
  refine ⟨⟨{1, x}, by rw [h.span L]; simp⟩, eq_top_iff.2 fun w _ => ?_⟩
  have h0 := h.im_ne
  rw [show w = (w.re - w.im / x.im * x.re) • (1 : Etau K τ) + (w.im / x.im) • x by
    ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]; field_simp]
  exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span isIntegral_one)) (Submodule.smul_mem _ _ (Submodule.subset_span h.int))

end UpperTheory.V.Z.Sym.Loc.PK
