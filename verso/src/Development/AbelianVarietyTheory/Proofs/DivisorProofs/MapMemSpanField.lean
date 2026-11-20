import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

namespace GlobalTheory.StandardLatticeSpan

open NumberField

variable {E E' : Type} [Field E] [Field E'] (f : E ≃+* E') {n : ℕ}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc⟩`. Establish `h1 : IsIntegral ℤ (f a)` using `hc ▸ c.isIntegral_coe`. Establish `h2 : IsIntegral ℤ (f.symm (f a))` using `map_isIntegral_int (f.symm : E' →+* E) h1`. Rewrite `h2` using `[f.symm_apply_apply]`.

Conclude with `⟨⟨a, h2⟩, rfl⟩`. Introduce and unpack `⟨c, rfl⟩`. Conclude with `⟨⟨f (algebraMap _ _ c), map_isIntegral_int (f : E →+* E') c.isIntegral_coe⟩, rfl⟩`.
-/
theorem mem_range_iff (a : E) :
    f a ∈ (algebraMap (𝓞 E') E').range ↔ a ∈ (algebraMap (𝓞 E) E).range := by
  constructor
  · rintro ⟨c, hc⟩
    have h1 : IsIntegral ℤ (f a) := hc ▸ c.isIntegral_coe
    have h2 : IsIntegral ℤ (f.symm (f a)) :=
      map_isIntegral_int (f.symm : E' →+* E) h1
    rw [f.symm_apply_apply] at h2
    exact ⟨⟨a, h2⟩, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨⟨f (algebraMap _ _ c), map_isIntegral_int (f : E →+* E') c.isIntegral_coe⟩, rfl⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => exact hy`. Consider the case `zero => exact ⟨0, L.zero_mem, by ext i; simp⟩`.

Consider the case `add y z _ _ hy hz`. Take `⟨a, ha, rfl⟩` from `hy`. Take `⟨b, hb, rfl⟩` from `hz`. Conclude with `⟨a + b, L.add_mem ha hb, by ext i; simp⟩`. Consider the case `smul c y _ hy`.

Take `⟨a, ha, rfl⟩` from `hy`. Take `⟨d, hd⟩` from `(mem_range_iff f (f.symm (algebraMap (𝓞 E') E' c))).1 ⟨c, by rw [f.apply_symm_apply]⟩`. Use `⟨d • a, L.smul_mem d ha, ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Simplify using `only [Pi.smul_apply, Algebra.smul_def, map_mul, hd, RingEquiv.apply_symm_apply]`.

Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `Submodule.subset_span ⟨x, hx, rfl⟩`.
-/
theorem mem_span_iff (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E') :
    y ∈ Submodule.span (𝓞 E') ((fun (x : Fin n → E) (i : Fin n) ↦ f (x i)) '' (L : Set (Fin n → E)))
      ↔ ∃ x ∈ L, (fun i ↦ f (x i)) = y := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => exact ⟨0, L.zero_mem, by ext i; simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, ha, rfl⟩ := hy
      obtain ⟨b, hb, rfl⟩ := hz
      exact ⟨a + b, L.add_mem ha hb, by ext i; simp⟩
    | smul c y _ hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      obtain ⟨d, hd⟩ := (mem_range_iff f (f.symm (algebraMap (𝓞 E') E' c))).1
        ⟨c, by rw [f.apply_symm_apply]⟩
      refine ⟨d • a, L.smul_mem d ha, ?_⟩
      ext i
      simp only [Pi.smul_apply, Algebra.smul_def, map_mul, hd, RingEquiv.apply_symm_apply]
  · rintro ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨x, hx, rfl⟩

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩`. Consider the case `zero`. Establish `: (fun i ↦ f ((0 : Fin n → E) i)) = 0` using `by ext i; simp`. Rewrite using `[this]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add y z _ _ hy hz`. Establish `: (fun i ↦ f ((y + z) i)) = (fun i ↦ f (y i)) + (fun i ↦ f (z i))` using `by ext i; simp`. Rewrite using `[this]`. Conclude with `Submodule.add_mem _ hy hz`.

Consider the case `smul c y _ hy`. Take `⟨d, hd⟩` from `(mem_range_iff f (algebraMap (𝓞 E) E c)).2 ⟨c, rfl⟩`. Establish `: (fun i ↦ f ((c • y) i)) = d • (fun i ↦ f (y i))`. Use extensionality with `i`. Simplify using `only [Pi.smul_apply, Algebra.smul_def, map_mul, hd]`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem map_mem_span_int (s : Set (Fin n → E)) {x : Fin n → E}
    (hx : x ∈ Submodule.span (𝓞 E) s) :
    (fun i ↦ f (x i)) ∈
      Submodule.span (𝓞 E') ((fun (x : Fin n → E) (i : Fin n) ↦ f (x i)) '' s) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero =>
    have : (fun i ↦ f ((0 : Fin n → E) i)) = 0 := by ext i; simp
    rw [this]; exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    have : (fun i ↦ f ((y + z) i)) = (fun i ↦ f (y i)) + (fun i ↦ f (z i)) := by ext i; simp
    rw [this]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    obtain ⟨d, hd⟩ := (mem_range_iff f (algebraMap (𝓞 E) E c)).2 ⟨c, rfl⟩
    have : (fun i ↦ f ((c • y) i)) = d • (fun i ↦ f (y i)) := by
      ext i
      simp only [Pi.smul_apply, Algebra.smul_def, map_mul, hd]
    rw [this]; exact Submodule.smul_mem _ _ hy

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩`. Consider the case `zero`. Establish `: (fun i ↦ f ((0 : Fin n → E) i)) = 0` using `by ext i; simp`. Rewrite using `[this]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add y z _ _ hy hz`. Establish `: (fun i ↦ f ((y + z) i)) = (fun i ↦ f (y i)) + (fun i ↦ f (z i))` using `by ext i; simp`. Rewrite using `[this]`. Conclude with `Submodule.add_mem _ hy hz`.

Consider the case `smul c y _ hy`. Establish `: (fun i ↦ f ((c • y) i)) = f c • (fun i ↦ f (y i))`. Use extensionality with `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul]`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem map_mem_span_field (s : Set (Fin n → E)) {x : Fin n → E}
    (hx : x ∈ Submodule.span E s) :
    (fun i ↦ f (x i)) ∈
      Submodule.span E' ((fun (x : Fin n → E) (i : Fin n) ↦ f (x i)) '' s) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero =>
    have : (fun i ↦ f ((0 : Fin n → E) i)) = 0 := by ext i; simp
    rw [this]; exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    have : (fun i ↦ f ((y + z) i)) = (fun i ↦ f (y i)) + (fun i ↦ f (z i)) := by ext i; simp
    rw [this]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    have : (fun i ↦ f ((c • y) i)) = f c • (fun i ↦ f (y i)) := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rw [this]; exact Submodule.smul_mem _ _ hy

/- English proof (translation)
Simplify using `only [Formalism.BasicNotions.stdH, map_sum, map_mul, hf]`.
-/
theorem stdH_map [StarRing E] [StarRing E'] (hf : ∀ x : E, f (star x) = star (f x))
    (x y : Fin n → E) :
    Formalism.BasicNotions.stdH E' n (fun i ↦ f (x i)) (fun i ↦ f (y i)) = f (Formalism.BasicNotions.stdH E n x y) := by
  simp only [Formalism.BasicNotions.stdH, map_sum, map_mul, hf]

/- English proof (translation)
Take `⟨⟨s, hs⟩, htop, hdual⟩` from `hL`. Establish `surj : ∀ y : Fin n → E', ∃ x : Fin n → E, (fun i ↦ f (x i)) = y` using `fun y => ⟨fun i => f.symm (y i), by ext i; simp⟩`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.fg_def]`. Use `⟨(fun (x : Fin n → E) (i : Fin n) ↦ f (x i)) '' (s : Set (Fin n → E)), s.finite_toSet.image _, le_antisymm ?_ ?_⟩` and prove the remaining obligations.

Apply `Submodule.span_mono` to reduce the goal to its premises. Apply `Set.image_mono` to reduce the goal to its premises. Rewrite using `[← hs]`. Conclude with `Submodule.subset_span`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `map_mem_span_int f _ (hs ▸ hx)`. Rewrite using `[eq_top_iff]`. Introduce `y _`. Take `⟨x, rfl⟩` from `surj y`.

Establish `hx : x ∈ Submodule.span E (L : Set (Fin n → E))` using `htop ▸ Submodule.mem_top`. Conclude with `Submodule.span_mono Submodule.subset_span (map_mem_span_field f _ hx)`. Introduce `y`. Take `⟨y, rfl⟩` from `surj y`. Prove the components needed by the constructor for the conclusion.

Introduce `hy x hx`. Take `⟨y', hy', e⟩` from `(mem_span_iff f L _).1 hy`. Take `⟨x, hx', rfl⟩` from `(mem_span_iff f L _).1 hx`. Rewrite using `[← e, stdH_map f hf, mem_range_iff]`. Conclude with `(hdual y').1 hy' x hx'`.

Introduce `h`. Use `(mem_span_iff f L _).2 ⟨y, (hdual y).2 fun x hx => ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[← mem_range_iff f, ← stdH_map f hf]`. Conclude with `h _ ((mem_span_iff f L _).2 ⟨x, hx, rfl⟩)`.
-/
theorem isSDLat_map {E E' : Type} [Field E] [Field E'] (f : E ≃+* E') {n : ℕ}
    [NumberField E] [NumberField E'] [StarRing E] [StarRing E']
    (hf : ∀ x : E, f (star x) = star (f x)) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Formalism.BasicNotions.IsSDLat E n L) :
    Formalism.BasicNotions.IsSDLat E' n (Submodule.span (𝓞 E')
      ((fun (x : Fin n → E) (i : Fin n) ↦ f (x i)) '' (L : Set (Fin n → E)))) := by
  obtain ⟨⟨s, hs⟩, htop, hdual⟩ := hL
  have surj : ∀ y : Fin n → E', ∃ x : Fin n → E, (fun i ↦ f (x i)) = y :=
    fun y => ⟨fun i => f.symm (y i), by ext i; simp⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [Submodule.fg_def]
    refine ⟨(fun (x : Fin n → E) (i : Fin n) ↦ f (x i)) '' (s : Set (Fin n → E)),
      s.finite_toSet.image _, le_antisymm ?_ ?_⟩
    · apply Submodule.span_mono
      apply Set.image_mono
      rw [← hs]; exact Submodule.subset_span
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      exact map_mem_span_int f _ (hs ▸ hx)
  · rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := surj y
    have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := htop ▸ Submodule.mem_top
    exact Submodule.span_mono Submodule.subset_span (map_mem_span_field f _ hx)
  · intro y
    obtain ⟨y, rfl⟩ := surj y
    constructor
    · intro hy x hx
      obtain ⟨y', hy', e⟩ := (mem_span_iff f L _).1 hy
      obtain ⟨x, hx', rfl⟩ := (mem_span_iff f L _).1 hx
      rw [← e, stdH_map f hf, mem_range_iff]
      exact (hdual y').1 hy' x hx'
    · intro h
      refine (mem_span_iff f L _).2 ⟨y, (hdual y).2 fun x hx => ?_, rfl⟩
      rw [← mem_range_iff f, ← stdH_map f hf]
      exact h _ ((mem_span_iff f L _).2 ⟨x, hx, rfl⟩)

end GlobalTheory.StandardLatticeSpan
