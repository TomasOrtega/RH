import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.AddMulSelfEqOfOrthogonalIdempotents

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

open PositivityTheory.RgUd.TP.Desc.Piece

section
variable {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q)
  {x : Matrix (Fin N) (Fin N) k}

def Nx (x : Matrix (Fin N) (Fin N) k) : Submodule k (Matrix (Fin N) (Fin N) k) :=
  (Cx Z x).toSubmodule.map (LinearMap.mulLeft k (pe D.b x))

/- English proof (translation)
The claim follows from `Algebra.subset_adjoin ⟨j, rfl⟩`.
-/
theorem s_mem (j : Fin D.r) : pe (D.a j) x ∈ Sx D x := Algebra.subset_adjoin ⟨j, rfl⟩

/- English proof (translation)
The claim follows from `Algebra.adjoin_le (by rintro _ ⟨j, rfl⟩; exact pe_mem (D.ha j))`.
-/
theorem sx_le : Sx D x ≤ Cx Z x := Algebra.adjoin_le (by rintro _ ⟨j, rfl⟩; exact pe_mem (D.ha j))

/- English proof (translation)
Take `⟨h1, h2, -⟩` from `D.spec x hx hχ`. Apply `le_antisymm` to reduce the goal to its premises. Set `P : Subalgebra k (Matrix (Fin N) (Fin N) k)` to `(Submodule.span k (Set.range fun j => pe (D.a j) x)).toSubalgebra ?one ?mul`. Establish `hle : Sx D x ≤ P`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations.

Introduce `y hy`. Conclude with `Submodule.subset_span hy`. Introduce `y hy`. Conclude with `hle hy`. Use `case one =>`.

Rewrite using `[← h2]`. Use `Submodule.sum_mem _ ?_` and prove the remaining obligations. Introduce `j _`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`. Use `case mul =>`.

Introduce `a b ha hb`. Establish `hab : a * b ∈ Submodule.span k (Set.range fun j => pe (D.a j) x) * Submodule.span k (Set.range fun j => pe (D.a j) x)` using `Submodule.mul_mem_mul ha hb`. Rewrite `hab` using `[Submodule.span_mul_span]`. Use `(Submodule.span_le.2 ?_) hab` and prove the remaining obligations. Introduce and unpack `_ ⟨u, ⟨i, rfl⟩, v, ⟨j, rfl⟩, rfl⟩`.

Establish `e` using `h1 i j`. Simplify using `only at e ⊢`. Rewrite using `[e]`. Use `Submodule.sum_mem _ ?_` and prove the remaining obligations. Introduce `t _`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce `y hy`. Conclude with `Algebra.subset_adjoin hy`.
-/
theorem sx_toSub (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) :
    (Sx D x).toSubmodule = Submodule.span k (Set.range fun j => pe (D.a j) x) := by
  obtain ⟨h1, h2, -⟩ := D.spec x hx hχ
  apply le_antisymm
  · let P : Subalgebra k (Matrix (Fin N) (Fin N) k) :=
      (Submodule.span k (Set.range fun j => pe (D.a j) x)).toSubalgebra ?one ?mul
    · have hle : Sx D x ≤ P := by
        refine Algebra.adjoin_le ?_
        intro y hy
        exact Submodule.subset_span hy
      intro y hy
      exact hle hy
    case one =>
      rw [← h2]
      refine Submodule.sum_mem _ ?_
      intro j _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    case mul =>
      intro a b ha hb
      have hab : a * b ∈ Submodule.span k (Set.range fun j => pe (D.a j) x) *
          Submodule.span k (Set.range fun j => pe (D.a j) x) := Submodule.mul_mem_mul ha hb
      rw [Submodule.span_mul_span] at hab
      refine (Submodule.span_le.2 ?_) hab
      rintro _ ⟨u, ⟨i, rfl⟩, v, ⟨j, rfl⟩, rfl⟩
      have e := h1 i j
      simp only at e ⊢
      rw [e]
      refine Submodule.sum_mem _ ?_
      intro t _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  · refine Submodule.span_le.2 ?_
    intro y hy
    exact Algebra.subset_adjoin hy

/- English proof (translation)
Take `⟨-, -, -, -, -, hred, -⟩` from `D.spec x hx hχ`. Introduce `y hy hn`. Establish `: y ∈ (Sx D x).toSubmodule` using `hy`. Rewrite `this` using `[sx_toSub D hx hχ]`. Conclude with `hred y this hn`.
-/
theorem sx_nil (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) : ∀ y ∈ Sx D x, IsNilpotent y → y = 0 := by
  obtain ⟨-, -, -, -, -, hred, -⟩ := D.spec x hx hχ
  intro y hy hn
  have : y ∈ (Sx D x).toSubmodule := hy
  rw [sx_toSub D hx hχ] at this
  exact hred y this hn

/- English proof (translation)
Use `⟨fun a ha b hb => cx_comm hZ hx a (sx_le D ha) b (sx_le D hb), ⟨fun y hy => ?_⟩⟩` and prove the remaining obligations. Conclude with `Subtype.ext (sx_nil D hx hχ y.1 y.2 (hy.map (Sx D x).val))`.
-/
theorem sx_cr (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) : CR (Sx D x) := by
  refine ⟨fun a ha b hb => cx_comm hZ hx a (sx_le D ha) b (sx_le D hb), ⟨fun y hy => ?_⟩⟩
  exact Subtype.ext (sx_nil D hx hχ y.1 y.2 (hy.map (Sx D x).val))

/- English proof (translation)
Use `Submodule.map_le_iff_le_comap.2 ?_` and prove the remaining obligations. Introduce `y hy`. Rewrite using `[Submodule.mem_comap, LinearMap.mulLeft_apply]`. Conclude with `(Cx Z x).mul_mem (pe_mem D.hb) hy`.
-/
theorem nx_le : Nx D x ≤ (Cx Z x).toSubmodule := by
  refine Submodule.map_le_iff_le_comap.2 ?_
  intro y hy
  rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
  exact (Cx Z x).mul_mem (pe_mem D.hb) hy

/- English proof (translation)
Take `⟨-, -, -, -, hεq, -⟩` from `D.spec x hx hχ`. Introduce and unpack `_ ⟨c, hc, rfl⟩`. Use `⟨q, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.mulLeft_apply]`. Rewrite using `[(Commute.mul_pow (cx_comm hZ hx _ (pe_mem D.hb) c hc) q), hεq, zero_mul]`.
-/
theorem nx_nil (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) : ∀ n ∈ Nx D x, IsNilpotent n := by
  obtain ⟨-, -, -, -, hεq, -⟩ := D.spec x hx hχ
  rintro _ ⟨c, hc, rfl⟩
  refine ⟨q, ?_⟩
  simp only [LinearMap.mulLeft_apply]
  rw [(Commute.mul_pow (cx_comm hZ hx _ (pe_mem D.hb) c hc) q), hεq, zero_mul]

/- English proof (translation)
Introduce `c hc n hn`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.1 hn`. Use `Submodule.mem_map.2 ⟨c * y, (Cx Z x).mul_mem hc hy, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, ← mul_assoc, ← mul_assoc, cx_comm hZ hx _ hc _ (pe_mem D.hb)]`.
-/
theorem nx_mul (hZ : CR Z) (hx : x ∈ Bz Z) : ∀ c ∈ Cx Z x, ∀ n ∈ Nx D x, c * n ∈ Nx D x := by
  intro c hc n hn
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hn
  refine Submodule.mem_map.2 ⟨c * y, (Cx Z x).mul_mem hc hy, ?_⟩
  rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, ← mul_assoc, ← mul_assoc,
    cx_comm hZ hx _ hc _ (pe_mem D.hb)]

/- English proof (translation)
Simplify using `only [re]`. Use `Submodule.sum_mem _ ?_` and prove the remaining obligations. Introduce `l _`. Use `Submodule.sum_mem _ ?_` and prove the remaining obligations. Introduce `j _`.

Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `h | ⟨m, hm⟩ : (l : ℕ) = 0 ∨ ∃ m, (l : ℕ) = m + 1 := by`. Break down `(l : ℕ) with _ | m` into its components or cases. Conclude with `Or.inl rfl`. Conclude with `Or.inr ⟨m, rfl⟩`.

Rewrite using `[h, pow_zero, mul_one]`. Conclude with `Submodule.mem_sup_left (s_mem D j)`. Establish `hs : pe (D.a j) x ∈ Cx Z x` using `pe_mem (D.ha j)`. Establish `he : pe D.b x ∈ Cx Z x` using `pe_mem D.hb`. Rewrite using `[hm, pow_succ', ← mul_assoc, cx_comm hZ hx _ hs _ he, mul_assoc]`.

Use `Submodule.mem_sup_right (Submodule.mem_map.2 ⟨pe (D.a j) x * pe D.b x ^ m, ?_, ?_⟩)` and prove the remaining obligations. Conclude with `(Cx Z x).mul_mem hs ((Cx Z x).pow_mem he m)`. Rewrite using `[LinearMap.mulLeft_apply]`.
-/
theorem re_mem (hZ : CR Z) (hx : x ∈ Bz Z) (γ' : Fin D.d → Fin D.r → k) :
    re γ' (fun j => pe (D.a j) x) (pe D.b x) ∈ (Sx D x).toSubmodule ⊔ Nx D x := by
  simp only [re]
  refine Submodule.sum_mem _ ?_
  intro l _
  refine Submodule.sum_mem _ ?_
  intro j _
  refine Submodule.smul_mem _ _ ?_
  obtain h | ⟨m, hm⟩ : (l : ℕ) = 0 ∨ ∃ m, (l : ℕ) = m + 1 := by
    rcases (l : ℕ) with _ | m
    · exact Or.inl rfl
    · exact Or.inr ⟨m, rfl⟩
  · rw [h, pow_zero, mul_one]
    exact Submodule.mem_sup_left (s_mem D j)
  · have hs : pe (D.a j) x ∈ Cx Z x := pe_mem (D.ha j)
    have he : pe D.b x ∈ Cx Z x := pe_mem D.hb
    rw [hm, pow_succ', ← mul_assoc, cx_comm hZ hx _ hs _ he, mul_assoc]
    refine Submodule.mem_sup_right (Submodule.mem_map.2 ⟨pe (D.a j) x * pe D.b x ^ m, ?_, ?_⟩)
    · exact (Cx Z x).mul_mem hs ((Cx Z x).pow_mem he m)
    · rw [LinearMap.mulLeft_apply]

/- English proof (translation)
Take `⟨-, -, -, -, -, -, hz, -⟩` from `D.spec x hx hχ`. Rewrite using `[D.hz]`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[hz i]`.

Conclude with `re_mem D hZ hx (D.γ i)`.
-/
theorem z_le (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) : Z.toSubmodule ≤ (Sx D x).toSubmodule ⊔ Nx D x := by
  obtain ⟨-, -, -, -, -, -, hz, -⟩ := D.spec x hx hχ
  rw [D.hz]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  rw [hz i]
  exact re_mem D hZ hx (D.γ i)

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, hxb, -⟩` from `D.spec x hx hχ`. Use `re_mem D hZ hx D.β` as an intermediate fact. Rewrite `this` using `[← hxb]`. Then use the resulting hypothesis.
-/
theorem x_mem (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) : x ∈ (Sx D x).toSubmodule ⊔ Nx D x := by
  obtain ⟨-, -, -, -, -, -, -, hxb, -⟩ := D.spec x hx hχ
  have := re_mem D hZ hx D.β
  rwa [← hxb] at this

/- English proof (translation)
Establish `hfm : f ∈ (Sx D x).toSubmodule ⊔ Nx D x` using `z_le D hZ hx hχ hf`. Take `⟨s, hs, n, hn, hsn⟩` from `Submodule.mem_sup.1 hfm`. Establish `hsS : s ∈ Sx D x` using `hs`. Establish `hsC : s ∈ Cx Z x` using `sx_le D hsS`. Establish `hnC : n ∈ Cx Z x` using `nx_le D hn`.

Establish `hfC : f ∈ Cx Z x` using `z_le_cx hf`. Establish `hnn : IsNilpotent n` using `nx_nil D hZ hx hχ n hn`. Establish `cfn : Commute f n` using `cx_comm hZ hx f hfC n hnC`. Establish `cfs : Commute f s` using `cx_comm hZ hx f hfC s hsC`. Establish `hs_eq : s = f - n` using `by rw [← hsn]; abel`.

Establish `key : s * s - s = n * (n + 1 - 2 * f)`. Establish `e : (f - n) * (f - n) - (f - n) - n * (n + 1 - 2 * f) = (f * f - f) + (n * f - f * n)` using `by noncomm_ring`. Rewrite `e` using `[hfi.eq, cfn.eq, sub_self, sub_self, add_zero, sub_eq_zero]`. Rewrite using `[hs_eq]`. Conclude with `e`.

Establish `c2 : Commute n (2 * f)`. Rewrite using `[two_mul]`. Conclude with `cfn.symm.add_right cfn.symm`. Establish `cn2 : Commute n (n + 1 - 2 * f)` using `((Commute.refl n).add_right (Commute.one_right n)).sub_right c2`. Establish `hnil : IsNilpotent (s * s - s)`.

Rewrite using `[key]`. Conclude with `Commute.isNilpotent_mul_right cn2 hnn`. Establish `hz : s * s - s = 0` using `sx_nil D hx hχ _ (Subalgebra.sub_mem _ (Subalgebra.mul_mem _ hsS hsS) hsS) hnil`. Establish `hsi : IsIdempotentElem s` using `sub_eq_zero.1 hz`. Establish `hfs : f - s = n` using `by rw [← hsn]; abel`.

Establish `hfeq : f = s` using `eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute hfi hsi (by rw [hfs]; exact hnn) cfs`. Rewrite using `[hfeq]`. Conclude with `hsS`.
-/
theorem idem_mem (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) {f : Matrix (Fin N) (Fin N) k} (hf : f ∈ Z)
    (hfi : IsIdempotentElem f) : f ∈ Sx D x := by
  have hfm : f ∈ (Sx D x).toSubmodule ⊔ Nx D x := z_le D hZ hx hχ hf
  obtain ⟨s, hs, n, hn, hsn⟩ := Submodule.mem_sup.1 hfm
  have hsS : s ∈ Sx D x := hs
  have hsC : s ∈ Cx Z x := sx_le D hsS
  have hnC : n ∈ Cx Z x := nx_le D hn
  have hfC : f ∈ Cx Z x := z_le_cx hf
  have hnn : IsNilpotent n := nx_nil D hZ hx hχ n hn
  have cfn : Commute f n := cx_comm hZ hx f hfC n hnC
  have cfs : Commute f s := cx_comm hZ hx f hfC s hsC
  have hs_eq : s = f - n := by rw [← hsn]; abel
  have key : s * s - s = n * (n + 1 - 2 * f) := by
    have e : (f - n) * (f - n) - (f - n) - n * (n + 1 - 2 * f) = (f * f - f) + (n * f - f * n) := by
      noncomm_ring
    rw [hfi.eq, cfn.eq, sub_self, sub_self, add_zero, sub_eq_zero] at e
    rw [hs_eq]
    exact e
  have c2 : Commute n (2 * f) := by
    rw [two_mul]
    exact cfn.symm.add_right cfn.symm
  have cn2 : Commute n (n + 1 - 2 * f) :=
    ((Commute.refl n).add_right (Commute.one_right n)).sub_right c2
  have hnil : IsNilpotent (s * s - s) := by
    rw [key]
    exact Commute.isNilpotent_mul_right cn2 hnn
  have hz : s * s - s = 0 :=
    sx_nil D hx hχ _ (Subalgebra.sub_mem _ (Subalgebra.mul_mem _ hsS hsS) hsS) hnil
  have hsi : IsIdempotentElem s := sub_eq_zero.1 hz
  have hfs : f - s = n := by rw [← hsn]; abel
  have hfeq : f = s :=
    eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute hfi hsi (by rw [hfs]; exact hnn) cfs
  rw [hfeq]
  exact hsS

end

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
