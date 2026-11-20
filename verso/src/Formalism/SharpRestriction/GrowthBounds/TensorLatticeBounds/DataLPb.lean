import Formalism.SharpRestriction.GrowthBounds.TensorLatticeBounds.DataLoc

noncomputable section

namespace Formalism.MainNotions.G.Inhab

open Formalism.MainNotions.G

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

def gen (Qq : Type) [Field Qq] (p : ℕ) (a : ℤ) : Fin 1 → Qq := fun _ => (p : Qq) ^ a

/- English proof (translation)
The claim follows from `Submodule.mem_span_singleton_self _`.
-/
theorem gen_mem (a : ℤ) : gen Qq p a ∈ line W (Qq := Qq) p a := Submodule.mem_span_singleton_self _

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [gen, Pi.smul_apply, Algebra.smul_def, map_natCast]`. Rewrite using `[zpow_add₀ (p_ne h), zpow_one, mul_comm]`.
-/
theorem p_smul_gen (h : HidaSetting p n' W Qq O Kf ι σ j w) (a : ℤ) : (p : W) • gen Qq p a = gen Qq p (a + 1) := by
  funext i
  simp only [gen, Pi.smul_apply, Algebra.smul_def, map_natCast]
  rw [zpow_add₀ (p_ne h), zpow_one, mul_comm]

/- English proof (translation)
Unfold `line`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`. Use `p_smul_gen (W := W) h a` as an intermediate fact. Unfold `gen at this`. Rewrite using `[← this]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)`.
-/
theorem line_succ_le (h : HidaSetting p n' W Qq O Kf ι σ j w) (a : ℤ) : line W (Qq := Qq) p (a + 1) ≤ line W p a := by
  unfold line
  rw [Submodule.span_le, Set.singleton_subset_iff]
  have := p_smul_gen (W := W) h a
  unfold gen at this
  rw [← this]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/- English proof (translation)
Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hx`. Rewrite using `[smul_comm]`. Use `p_smul_gen (W := W) h a` as an intermediate fact. Unfold `gen at this`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)`.
-/
theorem p_smul_line (h : HidaSetting p n' W Qq O Kf ι σ j w) (a : ℤ) (x : Fin 1 → Qq) (hx : x ∈ line W (Qq := Qq) p a) :
    (p : W) • x ∈ line W (Qq := Qq) p (a + 1) := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
  rw [smul_comm]
  have := p_smul_gen (W := W) h a
  unfold gen at this
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

def toQuot (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] (p : ℕ) (a : ℤ) :
    W →ₗ[W] (↥(line W (Qq := Qq) p a) ⧸ Submodule.comap (line W (Qq := Qq) p a).subtype (line W p (a + 1))) :=
  (Submodule.mkQ _).comp (LinearMap.toSpanSingleton W _ ⟨gen Qq p a, Submodule.mem_span_singleton_self _⟩)

/- English proof (translation)
Introduce `y`. Take `⟨⟨x, hx⟩, rfl⟩` from `Submodule.mkQ_surjective _ y`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hx`. Conclude with `⟨c, rfl⟩`.
-/
theorem toQuot_surj (a : ℤ) : Function.Surjective (toQuot W (Qq := Qq) p a) := by
  intro y
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
  exact ⟨c, rfl⟩

/- English proof (translation)
Use `h.frac_alt` as an intermediate fact. Use extensionality with `c`. Rewrite using `[LinearMap.mem_ker, Ideal.mem_span_singleton]`. Use `show Submodule.mkQ _ (c • (⟨gen Qq p a, gen_mem a⟩ : ↥(line W (Qq := Qq) p a))) = 0 ↔ _`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`.

Use `show c • gen Qq p a ∈ line W p (a + 1) ↔ _`. Prove the components needed by the constructor for the conclusion. Introduce `hc`. Take `⟨d, hd⟩` from `Submodule.mem_span_singleton.1 hc`. Establish `hd' : d • gen Qq p (a + 1) = c • gen Qq p a` using `hd`.

Rewrite `hd'` using `[← p_smul_gen (W := W) h a, smul_smul]`. Establish `h0` using `congrFun hd' 0`. Simplify using `only [gen, Pi.smul_apply, Algebra.smul_def] at h0`. Establish `h1` using `mul_right_cancel₀ (zpow_ne_zero a (p_ne h)) h0`. Establish `h2 : d * (p : W) = c` using `IsFractionRing.injective W Qq h1`.

Conclude with `⟨d, by rw [← h2, mul_comm]⟩`. Introduce and unpack `⟨d, rfl⟩`. Rewrite using `[mul_comm, mul_smul, p_smul_gen h]`. Conclude with `Submodule.smul_mem _ _ (gen_mem _)`.
-/
theorem toQuot_ker (h : HidaSetting p n' W Qq O Kf ι σ j w) (a : ℤ) :
    LinearMap.ker (toQuot W (Qq := Qq) p a) = Ideal.span {(p : W)} := by
  have := h.frac_alt
  ext c
  rw [LinearMap.mem_ker, Ideal.mem_span_singleton]
  show Submodule.mkQ _ (c • (⟨gen Qq p a, gen_mem a⟩ : ↥(line W (Qq := Qq) p a))) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  show c • gen Qq p a ∈ line W p (a + 1) ↔ _
  constructor
  · intro hc
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 hc
    have hd' : d • gen Qq p (a + 1) = c • gen Qq p a := hd
    rw [← p_smul_gen (W := W) h a, smul_smul] at hd'
    have h0 := congrFun hd' 0
    simp only [gen, Pi.smul_apply, Algebra.smul_def] at h0
    have h1 := mul_right_cancel₀ (zpow_ne_zero a (p_ne h)) h0
    have h2 : d * (p : W) = c := IsFractionRing.injective W Qq h1
    exact ⟨d, by rw [← h2, mul_comm]⟩
  · rintro ⟨d, rfl⟩
    rw [mul_comm, mul_smul, p_smul_gen h]
    exact Submodule.smul_mem _ _ (gen_mem _)

/- English proof (translation)
Rewrite using `[← h.res_card, ← toQuot_ker (Qq := Qq) h a]`. Conclude with `Nat.card_congr ((toQuot W (Qq := Qq) p a).quotKerEquivOfSurjective (toQuot_surj a)).symm.toEquiv`.
-/
theorem card_line_quot (h : HidaSetting p n' W Qq O Kf ι σ j w) (a : ℤ) :
    Nat.card (↥(line W (Qq := Qq) p a) ⧸ Submodule.comap (line W (Qq := Qq) p a).subtype (line W p (a + 1))) =
      p ^ n' := by
  rw [← h.res_card, ← toQuot_ker (Qq := Qq) h a]
  exact Nat.card_congr ((toQuot W (Qq := Qq) p a).quotKerEquivOfSurjective (toQuot_surj a)).symm.toEquiv

def edge1 (W : Type) (Qq : Type) [CommRing W] [Field Qq] [Algebra W Qq] (p : ℕ) (a : ℤ) : Edge W Qq 1 :=
  ⟨line W p (a + 1), line W p a⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨line_isLattice h _, line_isLattice h _, line_succ_le h a, p_smul_line h a, by rw [mul_one]; exact card_line_quot h a⟩`.
-/
theorem line_lattice_isEdge (h : HidaSetting p n' W Qq O Kf ι σ j w) (a : ℤ) : IsEdge p n' 1 (edge1 W Qq p a) :=
  ⟨line_isLattice h _, line_isLattice h _, line_succ_le h a, p_smul_line h a, by
    rw [mul_one]; exact card_line_quot h a⟩

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5⟩` from `he`. Take `⟨s, t⟩` from `e`. Take `⟨b, rfl⟩` from `lat1 h s h1`. Take `⟨a, rfl⟩` from `lat1 h t h2`. Establish `hab : a ≤ b` using `le_of_mem h (h3 (gen_mem b))`.

Establish `hba : b ≤ a + 1`. Use `h4 _ (gen_mem a)` as an intermediate fact. Rewrite `this` using `[p_smul_gen h]`. Conclude with `le_of_mem h this`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Break down `(by omega : b = a + 1 ∨ b = a) with rfl | rfl` into its components or cases. Both sides reduce to the same expression. It suffices to derive a contradiction. Establish `htop : Submodule.comap (line W (Qq` using `Qq) p b).subtype (line W p b) = ⊤ := Submodule.comap_subtype_self _`. Establish `h5' : Nat.card (↥(line W (Qq` using `Qq) p b) ⧸ Submodule.comap (line W (Qq := Qq) p b).subtype (line W p b)) = p ^ (n' * 1) := h5`.

Rewrite `h5'` using `[htop]`. Establish `h6 : Nat.card (↥(line W (Qq` using `Qq) p b) ⧸ (⊤ : Submodule W ↥(line W (Qq := Qq) p b))) = 1 := Nat.card_unique`. Rewrite `h5'` using `[h6]`. Establish `h7 : 1 < p ^ (n' * 1)` using `Nat.one_lt_pow (by have := h.two_le; omega) (by have := h.five_le; omega)`. Use linear arithmetic over natural numbers and integers.
-/
theorem edge_eq (h : HidaSetting p n' W Qq O Kf ι σ j w) (e : Edge W Qq 1) (he : IsEdge p n' 1 e) :
    ∃ a : ℤ, e = edge1 W Qq p a := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := he
  obtain ⟨s, t⟩ := e
  obtain ⟨b, rfl⟩ := lat1 h s h1
  obtain ⟨a, rfl⟩ := lat1 h t h2
  have hab : a ≤ b := le_of_mem h (h3 (gen_mem b))
  have hba : b ≤ a + 1 := by
    have := h4 _ (gen_mem a)
    rw [p_smul_gen h] at this
    exact le_of_mem h this
  refine ⟨a, ?_⟩
  rcases (by omega : b = a + 1 ∨ b = a) with rfl | rfl
  · rfl
  · exfalso
    have htop : Submodule.comap (line W (Qq := Qq) p b).subtype (line W p b) = ⊤ := Submodule.comap_subtype_self _
    have h5' : Nat.card (↥(line W (Qq := Qq) p b) ⧸ Submodule.comap (line W (Qq := Qq) p b).subtype (line W p b)) =
      p ^ (n' * 1) := h5
    rw [htop] at h5'
    have h6 : Nat.card (↥(line W (Qq := Qq) p b) ⧸ (⊤ : Submodule W ↥(line W (Qq := Qq) p b))) = 1 :=
      Nat.card_unique
    rw [h6] at h5'
    have h7 : 1 < p ^ (n' * 1) := Nat.one_lt_pow (by have := h.two_le; omega) (by have := h.five_le; omega)
    omega

end Formalism.MainNotions.G.Inhab

end
