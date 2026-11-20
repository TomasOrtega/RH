import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FibreParseval

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col

noncomputable section

variable {E : Type} [Field E] [NumberField E]

namespace ZM

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

/- English proof (translation)
Establish `hK` using `hK_of hI`. Establish `ho : Orthonormal ℂ (e (IR I))`. Rewrite using `[orthonormal_iff_ite]`. Introduce `i j`. Rewrite using `[← Hf_eq_inner, Hf_e hK]`.

Apply the tactic sequence `by_cases h : i = j <;> simp [h, eq_comm]`. Rewrite using `[span1, finrank_span_eq_card ho.linearIndependent, Fintype.card_fin]`.
-/
theorem finrank_span1 (hI : IsSplit P I) : Module.finrank ℂ (span1 (IR I)) = dK (IR I) := by
  have hK := hK_of hI
  have ho : Orthonormal ℂ (e (IR I)) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [← Hf_eq_inner, Hf_e hK]
    by_cases h : i = j <;> simp [h, eq_comm]
  rw [span1, finrank_span_eq_card ho.linearIndependent, Fintype.card_fin]

/- English proof (translation)
Establish `h1` using `Submodule.finrank_add_finrank_orthogonal (span1 (IR I))`. Rewrite `h1` using `[finrank_euclideanSpace, finrank_span1 hI]`. Rewrite using `[Fintype.card_fin, gB, V2, ← h1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dim_count (hI : IsSplit P I) :
    2 * Fintype.card (Idx X.dim) = dK (IR I) + (dK (IR I) + 2 * Fintype.card (Fin (gB (IR I)))) := by
  have h1 := Submodule.finrank_add_finrank_orthogonal (span1 (IR I))
  rw [finrank_euclideanSpace, finrank_span1 hI] at h1
  rw [Fintype.card_fin, gB, V2, ← h1]
  ring

def cp (hI : IsSplit P I) (j : Fin (Module.finrank ℝ (IR I))) : Vsp X.dim :=
  (dual_lift hI (Pi.single j 1)).choose

/- English proof (translation)
The claim follows from `(dual_lift hI (Pi.single j 1)).choose_spec.1`.
-/
theorem cp_mem (hI : IsSplit P I) (j) : cp hI j ∈ X.L := (dual_lift hI (Pi.single j 1)).choose_spec.1

/- English proof (translation)
The claim follows from `(dual_lift hI (Pi.single j 1)).choose_spec.2 i`.
-/
theorem cp_pair (hI : IsSplit P I) (j i) :
    (Hf (cp hI j) ((Ib hI i : IR I) : Vsp X.dim)).im = ((Pi.single j 1 : _ → ℤ) i : ℝ) := (dual_lift hI (Pi.single j 1)).choose_spec.2 i

/- English proof (translation)
Rewrite using `[← lat_bB hI hP]`. Conclude with `Submodule.subset_span ⟨l, rfl⟩`.
-/
theorem bB_mem_GB (hI : IsSplit P I) (hP : Ext.PackingCount) (l) : bB hI hP l ∈ GB X I := by
  rw [← lat_bB hI hP]; exact Submodule.subset_span ⟨l, rfl⟩

def cpp (hI : IsSplit P I) (hP : Ext.PackingCount) (l : Fin (2 * Fintype.card (Fin (gB (IR I))))) :
    Vsp X.dim :=
  (mem_GB.1 (bB_mem_GB hI hP l)).choose

/- English proof (translation)
The claim follows from `(mem_GB.1 (bB_mem_GB hI hP l)).choose_spec.1`.
-/
theorem cpp_mem (hI : IsSplit P I) (hP : Ext.PackingCount) (l) : cpp hI hP l ∈ Ip X I := (mem_GB.1 (bB_mem_GB hI hP l)).choose_spec.1

/- English proof (translation)
The claim follows from `(mem_GB.1 (bB_mem_GB hI hP l)).choose_spec.2`.
-/
theorem cpp_wmap (hI : IsSplit P I) (hP : Ext.PackingCount) (l) :
    wmap (IR I) (cpp hI hP l) = bB hI hP l := (mem_GB.1 (bB_mem_GB hI hP l)).choose_spec.2

def Bf (hI : IsSplit P I) (hP : Ext.PackingCount) :
    Fin (Module.finrank ℝ (IR I)) ⊕ (Fin (Module.finrank ℝ (IR I)) ⊕ Fin (2 * Fintype.card (Fin (gB (IR I))))) →
      Vsp X.dim :=
  Sum.elim (fun i => ((Ib hI i : IR I) : Vsp X.dim)) (Sum.elim (cp hI) (cpp hI hP))

/- English proof (translation)
Establish `h : (⟨a, mem_IR ha⟩ : IR I) ∈ Submodule.span ℤ (Set.range (Ib hI))`. Rewrite using `[Ib_span hI]`. Conclude with `ha`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).1 h`. Use `⟨c, ?_⟩` and prove the remaining obligations.

Use `congrArg Subtype.val hc` as an intermediate fact. Simplify `this` using `[Submodule.coe_sum]`.
-/
theorem mem_I_span (hI : IsSplit P I) {a : Vsp X.dim} (ha : a ∈ I) :
    ∃ c : Fin (Module.finrank ℝ (IR I)) → ℤ, ∑ i, c i • ((Ib hI i : IR I) : Vsp X.dim) = a := by
  have h : (⟨a, mem_IR ha⟩ : IR I) ∈ Submodule.span ℤ (Set.range (Ib hI)) := by
    rw [Ib_span hI]; exact ha
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 h
  refine ⟨c, ?_⟩
  have := congrArg Subtype.val hc
  simpa [Submodule.coe_sum] using this

/- English proof (translation)
Establish `hK` using `hK_of hI`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Break down `k with i | j | l` into its components or cases.

Conclude with `hI.le (Ib_mem hI i)`. Conclude with `cp_mem hI j`. Conclude with `(cpp_mem hI hP l).1`. Introduce `x hx`. Establish `hmem : ∀ v, v ∈ Set.range (Bf hI hP) → v ∈ Submodule.span ℤ (Set.range (Bf hI hP))` using `fun v hv => Submodule.subset_span hv`.

Establish `hb : ∀ i, ((Ib hI i : IR I) : Vsp X.dim) ∈ Submodule.span ℤ (Set.range (Bf hI hP))` using `fun i => hmem _ ⟨Sum.inl i, rfl⟩`. Establish `hc : ∀ j, cp hI j ∈ Submodule.span ℤ (Set.range (Bf hI hP))` using `fun j => hmem _ ⟨Sum.inr (Sum.inl j), rfl⟩`. Establish `hcc : ∀ l, cpp hI hP l ∈ Submodule.span ℤ (Set.range (Bf hI hP))` using `fun l => hmem _ ⟨Sum.inr (Sum.inr l), rfl⟩`. Use `choose m hm using fun i => X.integral x _ hx (hI.le (Ib_mem hI i))`. Use `set y := x - ∑ j, m j • cp hI j with hy`.

Establish `hyL : y ∈ X.L` using `X.L.sub_mem hx (X.L.sum_mem fun j _ => X.L.smul_mem _ (cp_mem hI j))`. Establish `hyb : ∀ i, (Hf y ((Ib hI i : IR I) : Vsp X.dim)).im = 0` using `fun i => by`. Rewrite using `[hy, Hf_sub_l, Complex.sub_im, Hf_sum_l, Complex.im_sum, hm i]`. Simplify using `only [← Int.cast_smul_eq_zsmul ℂ, Hf_smul_l, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero, cp_pair]`. Simplify using `[Pi.single_apply]`.

Establish `hyIp : y ∈ Ip X I`. Use `⟨hyL, fun a ha => ?_⟩` and prove the remaining obligations. Take `⟨c, rfl⟩` from `mem_I_span hI ha`. Rewrite using `[Hf_sum_r, Complex.im_sum]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← Int.cast_smul_eq_zsmul ℂ, Hf_smul_r]`. Simplify using `[Complex.mul_im, hyb i]`. Establish `hwy : wmap (IR I) y ∈ Submodule.span ℤ (Set.range (bB hI hP))`. Rewrite using `[← lat, lat_bB hI hP]`. Conclude with `wmap_mem_GB hyIp`.

Take `⟨k, hk⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).1 hwy`. Use `set z := y - ∑ l, k l • cpp hI hP l with hz`. Establish `hzIp : z ∈ Ip X I` using `(Ip X I).sub_mem hyIp ((Ip X I).sum_mem fun l _ => (Ip X I).smul_mem _ (cpp_mem hI hP l))`. Establish `hwz : wmap (IR I) z = 0`. Rewrite using `[hz, map_sub, map_sum, ← hk]`.

Simplify using `only [map_zsmul, cpp_wmap, sub_self]`. Establish `hp2 : p2 (IR I) z = 0`. Rewrite using `[← norm_eq_zero, ← norm_wmap hK, hwz, norm_zero]`. Take `⟨c, hc'⟩` from `mem_I_span hI (mem_of_proj_two_eq_zero hI hzIp hp2)`. Establish `hxe : x = z + ∑ l, k l • cpp hI hP l + ∑ j, m j • cp hI j` using `by rw [hz, hy]; abel`.

Rewrite using `[hxe, ← hc']`. Use `Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_` and prove the remaining obligations. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hb i)`. Conclude with `Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hcc l)`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hc j)`.
-/
theorem span_Bf (hI : IsSplit P I) (hP : Ext.PackingCount) :
    Submodule.span ℤ (Set.range (Bf hI hP)) = X.L := by
  have hK := hK_of hI
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rcases k with i | j | l
    · exact hI.le (Ib_mem hI i)
    · exact cp_mem hI j
    · exact (cpp_mem hI hP l).1
  · intro x hx
    have hmem : ∀ v, v ∈ Set.range (Bf hI hP) → v ∈ Submodule.span ℤ (Set.range (Bf hI hP)) :=
      fun v hv => Submodule.subset_span hv
    have hb : ∀ i, ((Ib hI i : IR I) : Vsp X.dim) ∈ Submodule.span ℤ (Set.range (Bf hI hP)) :=
      fun i => hmem _ ⟨Sum.inl i, rfl⟩
    have hc : ∀ j, cp hI j ∈ Submodule.span ℤ (Set.range (Bf hI hP)) :=
      fun j => hmem _ ⟨Sum.inr (Sum.inl j), rfl⟩
    have hcc : ∀ l, cpp hI hP l ∈ Submodule.span ℤ (Set.range (Bf hI hP)) :=
      fun l => hmem _ ⟨Sum.inr (Sum.inr l), rfl⟩
    choose m hm using fun i => X.integral x _ hx (hI.le (Ib_mem hI i))
    set y := x - ∑ j, m j • cp hI j with hy
    have hyL : y ∈ X.L := X.L.sub_mem hx (X.L.sum_mem fun j _ => X.L.smul_mem _ (cp_mem hI j))
    have hyb : ∀ i, (Hf y ((Ib hI i : IR I) : Vsp X.dim)).im = 0 := fun i => by
      rw [hy, Hf_sub_l, Complex.sub_im, Hf_sum_l, Complex.im_sum, hm i]
      simp only [← Int.cast_smul_eq_zsmul ℂ, Hf_smul_l, Complex.mul_im, Complex.intCast_re,
        Complex.intCast_im, zero_mul, add_zero, cp_pair]
      simp [Pi.single_apply]
    have hyIp : y ∈ Ip X I := by
      refine ⟨hyL, fun a ha => ?_⟩
      obtain ⟨c, rfl⟩ := mem_I_span hI ha
      rw [Hf_sum_r, Complex.im_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← Int.cast_smul_eq_zsmul ℂ, Hf_smul_r]
      simp [Complex.mul_im, hyb i]
    have hwy : wmap (IR I) y ∈ Submodule.span ℤ (Set.range (bB hI hP)) := by
      rw [← lat, lat_bB hI hP]; exact wmap_mem_GB hyIp
    obtain ⟨k, hk⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hwy
    set z := y - ∑ l, k l • cpp hI hP l with hz
    have hzIp : z ∈ Ip X I := (Ip X I).sub_mem hyIp ((Ip X I).sum_mem fun l _ =>
      (Ip X I).smul_mem _ (cpp_mem hI hP l))
    have hwz : wmap (IR I) z = 0 := by
      rw [hz, map_sub, map_sum, ← hk]
      simp only [map_zsmul, cpp_wmap, sub_self]
    have hp2 : p2 (IR I) z = 0 := by
      rw [← norm_eq_zero, ← norm_wmap hK, hwz, norm_zero]
    obtain ⟨c, hc'⟩ := mem_I_span hI (mem_of_proj_two_eq_zero hI hzIp hp2)
    have hxe : x = z + ∑ l, k l • cpp hI hP l + ∑ j, m j • cp hI j := by rw [hz, hy]; abel
    rw [hxe, ← hc']
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hb i)
    · exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hcc l)
    · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hc j)

/- English proof (translation)
Rewrite using `[← X.b.span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Establish `h : X.b i ∈ Submodule.span ℤ (Set.range (Bf hI hP))`. Rewrite using `[span_Bf hI hP]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`.

Conclude with `Submodule.span_le_restrictScalars ℤ ℝ _ h`.
-/
theorem top_le_span_Bf (hI : IsSplit P I) (hP : Ext.PackingCount) :
    ⊤ ≤ Submodule.span ℝ (Set.range (Bf hI hP)) := by
  rw [← X.b.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have h : X.b i ∈ Submodule.span ℤ (Set.range (Bf hI hP)) := by
    rw [span_Bf hI hP]; exact Submodule.subset_span ⟨i, rfl⟩
  exact Submodule.span_le_restrictScalars ℤ ℝ _ h

/- English proof (translation)
Apply `linearIndependent_of_top_le_span_of_card_eq_finrank (top_le_span_Bf hI hP)` to reduce the goal to its premises. Establish `h` using `dim_count hI`. Rewrite `h` using `[Fintype.card_fin]`. Rewrite using `[Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, Module.finrank_eq_card_basis X.b, Fintype.card_fin]`. Conclude with `h.symm`.
-/
theorem Bf_li (hI : IsSplit P I) (hP : Ext.PackingCount) : LinearIndependent ℝ (Bf hI hP) := by
  apply linearIndependent_of_top_le_span_of_card_eq_finrank (top_le_span_Bf hI hP)
  have h := dim_count hI
  rw [Fintype.card_fin] at h
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin,
    Module.finrank_eq_card_basis X.b, Fintype.card_fin]
  exact h.symm

def BB (hI : IsSplit P I) (hP : Ext.PackingCount) :
    Module.Basis (Fin (Module.finrank ℝ (IR I)) ⊕ (Fin (Module.finrank ℝ (IR I)) ⊕
      Fin (2 * Fintype.card (Fin (gB (IR I)))))) ℝ (Vsp X.dim) :=
  Module.Basis.mk (Bf_li hI hP) (top_le_span_Bf hI hP)

/- English proof (translation)
The claim follows from `Module.Basis.mk_apply _ _ _`.
-/
theorem BB_apply (hI : IsSplit P I) (hP : Ext.PackingCount) (k) : BB hI hP k = Bf hI hP k := Module.Basis.mk_apply _ _ _

/- English proof (translation)
Establish `h : ⇑(BB hI hP) = Bf hI hP` using `funext (BB_apply hI hP)`. Rewrite using `[h]`. Conclude with `span_Bf hI hP`.
-/
theorem lat_BB (hI : IsSplit P I) (hP : Ext.PackingCount) :
    Submodule.span ℤ (Set.range (BB hI hP)) = X.L := by
  have h : ⇑(BB hI hP) = Bf hI hP := funext (BB_apply hI hP)
  rw [h]
  exact span_Bf hI hP

end ZM

end

end ReciprocityTheory.ChartRestriction.G.I2
