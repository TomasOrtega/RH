import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.PieceTop

noncomputable section

namespace PositivityTheory.RgUd.TP.Desc.Piece.PAsm2

open Polynomial PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ, ih, pow_succ]`. Simplify using `only [mul_assoc, Units.inv_mul_cancel_left]`.
-/
theorem conj_pow' {N : ℕ} (g : GL (Fin N) k) (y : Matrix (Fin N) (Fin N) k) (n : ℕ) :
    (g.val * y * g⁻¹.val) ^ n = g.val * y ^ n * g⁻¹.val := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc, Units.inv_mul_cancel_left]

/- English proof (translation)
Use `letI : CommRing Z := { (inferInstance : Ring ↥Z) with mul_comm := fun a b => Subtype.ext (hZ.1 a a.2 b b.2) }`. Use `haveI : IsReduced Z := hZ.2`. Use `haveI : IsArtinianRing Z := IsArtinianRing.of_finite k Z`. Establish `hT : {c : Z | aeval c χ = 0}.Finite`. Use `Set.Finite.of_finite_image ?_ (IsArtinianRing.equivPi Z).injective.injOn` and prove the remaining obligations.

Use `(Set.Finite.pi (t := fun I : MaximalSpectrum Z => χ.rootSet (Z ⧸ I.asIdeal)) fun I => χ.rootSet_finite _).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨c, hc, rfl⟩`. Use `Set.mem_univ_pi.2 fun I => ?_` and prove the remaining obligations. Rewrite using `[mem_rootSet_of_ne hχ, IsArtinianRing.equivPi_apply]`. Establish `h` using `Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ k I.asIdeal) c χ`.

Rewrite `h` using `[show aeval c χ = 0 from hc, map_zero]`. Conclude with `h`. Use `(hT.image Subtype.val).subset ?_` and prove the remaining obligations. Introduce and unpack `c ⟨hc, h0⟩`. Use `⟨⟨c, hc⟩, ?_, rfl⟩` and prove the remaining obligations.

Use `show aeval (⟨c, hc⟩ : Z) χ = 0`. Conclude with `Subtype.ext (by rw [Polynomial.aeval_subalgebra_coe]; exact h0)`.
-/
theorem roots_finite {N : ℕ} {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} (hZ : CR Z) {χ : k[X]} (hχ : χ ≠ 0) :
    {c : Matrix (Fin N) (Fin N) k | c ∈ Z ∧ aeval c χ = 0}.Finite := by
  letI : CommRing Z := { (inferInstance : Ring ↥Z) with mul_comm := fun a b => Subtype.ext (hZ.1 a a.2 b b.2) }
  haveI : IsReduced Z := hZ.2
  haveI : IsArtinianRing Z := IsArtinianRing.of_finite k Z
  have hT : {c : Z | aeval c χ = 0}.Finite := by
    refine Set.Finite.of_finite_image ?_ (IsArtinianRing.equivPi Z).injective.injOn
    refine (Set.Finite.pi (t := fun I : MaximalSpectrum Z => χ.rootSet (Z ⧸ I.asIdeal))
      fun I => χ.rootSet_finite _).subset ?_
    rintro _ ⟨c, hc, rfl⟩
    refine Set.mem_univ_pi.2 fun I => ?_
    rw [mem_rootSet_of_ne hχ, IsArtinianRing.equivPi_apply]
    have h := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ k I.asIdeal) c χ
    rw [show aeval c χ = 0 from hc, map_zero] at h
    exact h
  refine (hT.image Subtype.val).subset ?_
  rintro c ⟨hc, h0⟩
  refine ⟨⟨c, hc⟩, ?_, rfl⟩
  show aeval (⟨c, hc⟩ : Z) χ = 0
  exact Subtype.ext (by rw [Polynomial.aeval_subalgebra_coe]; exact h0)

/- English proof (translation)
Establish `hxc : x * c = c * x` using `(hx c hc).symm`. Establish `hcomm : ∀ a ∈ ({x, c} : Set (Matrix (Fin N) (Fin N) k)), ∀ b ∈ ({x, c} : Set (Matrix (Fin N) (Fin N) k)), a * b = b * a`. Introduce `a ha b hb`. Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb`. Apply the tactic sequence `rcases ha with rfl | rfl <;> rcases hb with rfl | rfl`.

Both sides reduce to the same expression. Conclude with `hxc`. Conclude with `hxc.symm`. Both sides reduce to the same expression. Use `letI : CommRing (Algebra.adjoin k ({x, c} : Set (Matrix (Fin N) (Fin N) k))) := Algebra.adjoinCommRingOfComm k hcomm`.

Set `A` to `Algebra.adjoin k ({x, c} : Set (Matrix (Fin N) (Fin N) k))`. Set `xa : A` to `⟨x, Algebra.subset_adjoin (by simp)⟩`. Set `ca : A` to `⟨c, Algebra.subset_adjoin (by simp)⟩`. Establish `hna : IsNilpotent (xa - ca)` using `(IsNilpotent.map_iff (f := A.val) Subtype.val_injective).1 hn`. Establish `h1` using `isNilpotent_aeval_sub_of_isNilpotent_sub χ hna`.

Establish `h2 : aeval xa χ = 0` using `Subtype.ext (by rw [Polynomial.aeval_subalgebra_coe]; exact hχx)`. Establish `h3 : IsNilpotent (aeval ca χ)` using `by simpa [h2] using h1.neg`. Establish `h4 : IsNilpotent (aeval c χ)`. Use `h3.map A.val` as an intermediate fact. Rewrite `this` using `[← Polynomial.aeval_algHom_apply]`. Then use the resulting hypothesis.

Set `c' : Z` to `⟨c, hc⟩`. Establish `h5 : IsNilpotent (aeval c' χ)`. Use `(IsNilpotent.map_iff (f := Z.val) Subtype.val_injective).1 ?_` and prove the remaining obligations. Rewrite using `[← Polynomial.aeval_algHom_apply]`. Conclude with `h4`.

Establish `h6 : aeval c' χ = 0` using `by haveI : IsReduced Z := hZ.2`. Conclude with `h5.eq_zero`. Establish `h7` using `congrArg Subtype.val h6`. Rewrite `h7` using `[Polynomial.aeval_subalgebra_coe]`. Then use the resulting hypothesis.
-/
theorem root_of_nil {N : ℕ} {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} (hZ : CR Z) {χ : k[X]}
    {x c : Matrix (Fin N) (Fin N) k} (hx : x ∈ Bz Z) (hc : c ∈ Z) (hχx : aeval x χ = 0)
    (hn : IsNilpotent (x - c)) : aeval c χ = 0 := by
  have hxc : x * c = c * x := (hx c hc).symm
  have hcomm : ∀ a ∈ ({x, c} : Set (Matrix (Fin N) (Fin N) k)), ∀ b ∈ ({x, c} : Set (Matrix (Fin N) (Fin N) k)),
      a * b = b * a := by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact hxc
    · exact hxc.symm
    · rfl
  letI : CommRing (Algebra.adjoin k ({x, c} : Set (Matrix (Fin N) (Fin N) k))) :=
    Algebra.adjoinCommRingOfComm k hcomm
  let A := Algebra.adjoin k ({x, c} : Set (Matrix (Fin N) (Fin N) k))
  let xa : A := ⟨x, Algebra.subset_adjoin (by simp)⟩
  let ca : A := ⟨c, Algebra.subset_adjoin (by simp)⟩
  have hna : IsNilpotent (xa - ca) := (IsNilpotent.map_iff (f := A.val) Subtype.val_injective).1 hn
  have h1 := isNilpotent_aeval_sub_of_isNilpotent_sub χ hna
  have h2 : aeval xa χ = 0 := Subtype.ext (by rw [Polynomial.aeval_subalgebra_coe]; exact hχx)
  have h3 : IsNilpotent (aeval ca χ) := by simpa [h2] using h1.neg
  have h4 : IsNilpotent (aeval c χ) := by
    have := h3.map A.val
    rwa [← Polynomial.aeval_algHom_apply] at this
  let c' : Z := ⟨c, hc⟩
  have h5 : IsNilpotent (aeval c' χ) := by
    refine (IsNilpotent.map_iff (f := Z.val) Subtype.val_injective).1 ?_
    rw [← Polynomial.aeval_algHom_apply]
    exact h4
  have h6 : aeval c' χ = 0 := by
    haveI : IsReduced Z := hZ.2
    exact h5.eq_zero
  have h7 := congrArg Subtype.val h6
  rwa [Polynomial.aeval_subalgebra_coe] at h7

variable (k) in

/- English proof (translation)
Introduce `p _ _ hU N q Z hZ hq hR hB χ`. Distinguish the cases in `hχ : χ.Monic ∧ χ.natDegree = N`. Use `swap`. Use `⟨0, Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0, fun x _ hc => ?_⟩, fun i => i.elim0⟩` and prove the remaining obligations. Conclude with `(hχ ⟨hc ▸ x.charpoly_monic, by rw [← hc, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]⟩).elim`.

Take `⟨D⟩` from `hS p N q Z hZ hq hR hB χ hχ.1 hχ.2`. Establish `hfin` using `roots_finite hZ hχ.1.ne_zero`. Establish `hrt : ∀ j : Fin hfin.toFinset.card, (hfin.toFinset.equivFin.symm j).1 ∈ Z ∧ aeval (hfin.toFinset.equivFin.symm j).1 χ = 0` using `fun j => hfin.mem_toFinset.1 (hfin.toFinset.equivFin.symm j).2`. Set `rt : Fin hfin.toFinset.card → Matrix (Fin N) (Fin N) k` to `fun j => (hfin.toFinset.equivFin.symm j).1`. Establish `rt_inj : Function.Injective rt` using `fun j j' h => hfin.toFinset.equivFin.symm.injective (Subtype.ext h)`.

Establish `hred : ∀ c ∈ Z, IsNilpotent c → c = 0` using `fun c hc hn => by`. Establish `h : IsNilpotent (⟨c, hc⟩ : Z)` using `(IsNilpotent.map_iff (f := Z.val) Subtype.val_injective).1 hn`. Use `haveI : IsReduced Z := hZ.2`. Conclude with `congrArg Subtype.val h.eq_zero`. Establish `hcz : ∀ c ∈ Z, ∀ x ∈ Bz Z, x - c ∈ Bz Z` using `fun c hc x hx a ha => by`.

Rewrite using `[mul_sub, sub_mul, hx a ha, hZ.1 a ha c hc]`. Set `e` to `(finFunctionFinEquiv (m := N + 1) (n := D.m)).symm`. Set `τ : Fin ((N + 1) ^ D.m) → Fin D.m → ℕ` to `fun i t => (e i t : ℕ)`. Establish `τ_inj : Function.Injective τ` using `fun i j h => e.injective (funext fun t => Fin.ext (congrFun h t))`. Set `bad : Fin ((N + 1) ^ D.m) → Prop` to `fun i => ∃ x₀ ∈ piece D (τ i), mu (Sx D x₀) < mu Z`.

Set `G : Fin ((N + 1) ^ D.m) × Option (Fin hfin.toFinset.card) → Set (Matrix (Fin N) (Fin N) k)` to `fun is => if bad is.1 then (if is.2 = none then piece D (τ is.1) else ∅) else is.2.elim ∅ (fun j => {x | x ∈ piece D (τ is.1) ∧ (x - rt j) ^ q = 0})`. Establish `hsub : ∀ is x, x ∈ G is → x ∈ piece D (τ is.1)`. Introduce and unpack `⟨i, s⟩ x hx`. Simplify using `only [G] at hx`. Use `split_ifs at hx`.

Conclude with `hx`. Simplify using `at hx`. Consider the cases of `s with`. Consider the case `none => simp at hx`. Consider the case `some j => exact hx.1`.

Establish `huniq : ∀ is js x, x ∈ G is → x ∈ G js → is = js`. Introduce and unpack `⟨i, s⟩ ⟨j, t⟩ x hx hy`. Establish `hij : i = j` using `τ_inj ((hsub _ x hx).2.2.symm.trans (hsub _ x hy).2.2)`. Substitute `hij` using the available equality. Establish `hxB : x ∈ Bz Z` using `(hsub _ x hx).1`.

Simplify using `only [G] at hx hy`. Distinguish the cases in `hb : bad i`. Rewrite `hx`, `hy`, `with`, `h1`, `h2` using `[if_pos hb] at hx hy split_ifs`. Rewrite using `[h1, h2]`. Simplify using `at hy`.

Simplify using `at hx`. Simplify using `at hx`. Rewrite `hx`, `hy` using `[if_neg hb]`. Consider the cases of `s with`. Consider the case `none => simp at hx`.

Consider the case `some a`. Consider the cases of `t with`. Consider the case `none => simp at hy`. Consider the case `some b`. Establish `ha : IsNilpotent (x - rt a)` using `⟨q, hx.2⟩`.

Establish `hb' : IsNilpotent (x - rt b)` using `⟨q, hy.2⟩`. Establish `hca : Commute (rt a) x` using `hxB _ (hrt a).1`. Establish `hcb : Commute (rt b) x` using `hxB _ (hrt b).1`. Establish `hab : Commute (rt b) (rt a)` using `hZ.1 _ (hrt b).1 _ (hrt a).1`. Establish `hcomm : Commute (x - rt b) (x - rt a)` using `((Commute.refl x).sub_right hca.symm).sub_left (hcb.sub_right hab)`.

Establish `hn : IsNilpotent (rt a - rt b)`. Use `hcomm.isNilpotent_sub hb' ha` as an intermediate fact. Rewrite `this` using `[sub_sub_sub_cancel_left]`. Then use the resulting hypothesis. Establish `h0` using `hred _ (Z.sub_mem (hrt a).1 (hrt b).1) hn`. Rewrite using `[rt_inj (sub_eq_zero.1 h0)]`.

Establish `hclosed : ∀ is, IsClosed (G is)`. Introduce and unpack `⟨i, s⟩`. Simplify using `only [G]`. Use `split_ifs`. Conclude with `(hP N q Z hZ χ D (τ i)).1`.

Conclude with `isClosed_empty`. Consider the cases of `s with`. Consider the case `none => exact isClosed_empty`. Consider the case `some j`. Conclude with `(hP N q Z hZ χ D (τ i)).1.inter (isClosed_eq ((continuous_id.sub continuous_const).pow q) continuous_const)`.

Establish `hinvar : ∀ is, ∀ g ∈ Gz Z, ∀ x ∈ G is, g.val * x * g⁻¹.val ∈ G is`. Introduce and unpack `⟨i, s⟩ g hg x hx`. Establish `hP2` using `(hP N q Z hZ χ D (τ i)).2.1 g hg`. Simplify using `only [G] at hx ⊢`. Use `split_ifs at hx ⊢`.

Conclude with `hP2 x hx`. Simplify using `at hx`. Consider the cases of `s with`. Consider the case `none => simp at hx`. Consider the case `some j`.

Use `⟨hP2 x hx.1, ?_⟩` and prove the remaining obligations. Establish `e1 : g.val * x * g⁻¹.val - rt j = g.val * (x - rt j) * g⁻¹.val`. Rewrite using `[mul_sub, sub_mul, ← hg (rt j) (hrt j).1, mul_assoc (rt j), Units.mul_inv, mul_one]`. Rewrite using `[e1, conj_pow', hx.2, mul_zero, zero_mul]`. Establish `hcover : ∀ x ∈ Bz Z, x.charpoly = χ → ∃ is, x ∈ G is`.

Introduce `x hx hc`. Establish `hle : ∀ t, typ D x t < N + 1` using `fun t => Nat.lt_succ_of_le ((Matrix.rank_le_width _).trans (by simp))`. Set `i` to `e.symm fun t => ⟨typ D x t, hle t⟩`. Establish `hxp : x ∈ piece D (τ i)` using `⟨hx, by rw [← hc]; exact Matrix.aeval_self_charpoly x, by funext t; simp [τ, i]⟩`. Distinguish the cases in `hb : bad i`.

Use `⟨(i, none), ?_⟩` and prove the remaining obligations. Simplify using `only [G, if_pos hb, if_true]`. Conclude with `hxp`. Break down `hD N q Z hZ χ D (τ i) x hxp with h | ⟨c, hc, hn⟩` into its components or cases. Conclude with `(hb ⟨x, hxp, h⟩).elim`.

Establish `hroot : aeval c χ = 0` using `root_of_nil hZ hx hc hxp.2.1 hn`. Establish `hmem : c ∈ hfin.toFinset` using `hfin.mem_toFinset.2 ⟨hc, hroot⟩`. Use `⟨(i, some (hfin.toFinset.equivFin ⟨c, hmem⟩)), ?_⟩` and prove the remaining obligations. Establish `hrtc : rt (hfin.toFinset.equivFin ⟨c, hmem⟩) = c` using `by simp [rt]`. Simplify using `only [G, if_neg hb, Option.elim_some]`.

Use `⟨hxp, ?_⟩` and prove the remaining obligations. Rewrite using `[hrtc]`. Conclude with `hB _ (hcz c hc x hx) hn`. Establish `hgood : ∀ is, Good Z (G is)`. Introduce and unpack `⟨i, s⟩`.

Simplify using `only [G]`. Use `split_ifs with h1`. Take `⟨x₀, hx₀, hlt⟩` from `h1`. Conclude with `Or.inr ⟨N, Sx D x₀, (hP N q Z hZ χ D (τ i)).2.2 x₀ hx₀, hlt, hT hF p hU N q Z hZ χ D (τ i) x₀ hx₀⟩`. Conclude with `Or.inl ⟨0, Z.zero_mem, fun x hx => by simp at hx⟩`.

Consider the cases of `s with`. Consider the case `none => exact Or.inl ⟨0, Z.zero_mem, fun x hx => by simp at hx⟩`. Consider the case `some j => exact Or.inl ⟨rt j, (hrt j).1, fun x hx => ⟨q, hx.2⟩⟩`. Set `eqv` to `Fintype.equivFin (Fin ((N + 1) ^ D.m) × Option (Fin hfin.toFinset.card))`. Use `⟨Fintype.card (Fin ((N + 1) ^ D.m) × Option (Fin hfin.toFinset.card)), fun i => G (eqv.symm i), ⟨fun i => ⟨hclosed _, fun x hx => (hsub _ x hx).1, hinvar _⟩, fun i j hij => Set.disjoint_left.2 fun x h1 h2 => hij (eqv.symm.injective (huniq _ _ x h1 h2)), fun x hx hc => ?_⟩, fun i …` and prove the remaining obligations.

Take `⟨is, his⟩` from `hcover x hx hc`. Conclude with `⟨eqv is, by simpa using his⟩`.
-/
theorem pieceGood_of (hF : PositivityTheory.PfBern.Frob.FrobeniusReciprocity) (hS : Sect k) (hP : PieceTop k) (hD : Dich k)
    (hT : Transfer k) : PieceGood k := by
  classical
  intro p _ _ hU N q Z hZ hq hR hB χ
  by_cases hχ : χ.Monic ∧ χ.natDegree = N
  swap
  · refine ⟨0, Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0, fun x _ hc => ?_⟩, fun i => i.elim0⟩
    exact (hχ ⟨hc ▸ x.charpoly_monic, by rw [← hc, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]⟩).elim
  obtain ⟨D⟩ := hS p N q Z hZ hq hR hB χ hχ.1 hχ.2
  have hfin := roots_finite hZ hχ.1.ne_zero
  have hrt : ∀ j : Fin hfin.toFinset.card, (hfin.toFinset.equivFin.symm j).1 ∈ Z ∧
      aeval (hfin.toFinset.equivFin.symm j).1 χ = 0 := fun j => hfin.mem_toFinset.1 (hfin.toFinset.equivFin.symm j).2
  let rt : Fin hfin.toFinset.card → Matrix (Fin N) (Fin N) k := fun j => (hfin.toFinset.equivFin.symm j).1
  have rt_inj : Function.Injective rt := fun j j' h => hfin.toFinset.equivFin.symm.injective (Subtype.ext h)
  have hred : ∀ c ∈ Z, IsNilpotent c → c = 0 := fun c hc hn => by
    have h : IsNilpotent (⟨c, hc⟩ : Z) := (IsNilpotent.map_iff (f := Z.val) Subtype.val_injective).1 hn
    haveI : IsReduced Z := hZ.2
    exact congrArg Subtype.val h.eq_zero
  have hcz : ∀ c ∈ Z, ∀ x ∈ Bz Z, x - c ∈ Bz Z := fun c hc x hx a ha => by
    rw [mul_sub, sub_mul, hx a ha, hZ.1 a ha c hc]
  let e := (finFunctionFinEquiv (m := N + 1) (n := D.m)).symm
  let τ : Fin ((N + 1) ^ D.m) → Fin D.m → ℕ := fun i t => (e i t : ℕ)
  have τ_inj : Function.Injective τ := fun i j h => e.injective (funext fun t => Fin.ext (congrFun h t))
  let bad : Fin ((N + 1) ^ D.m) → Prop := fun i => ∃ x₀ ∈ piece D (τ i), mu (Sx D x₀) < mu Z
  let G : Fin ((N + 1) ^ D.m) × Option (Fin hfin.toFinset.card) → Set (Matrix (Fin N) (Fin N) k) := fun is =>
    if bad is.1 then (if is.2 = none then piece D (τ is.1) else ∅)
    else is.2.elim ∅ (fun j => {x | x ∈ piece D (τ is.1) ∧ (x - rt j) ^ q = 0})
  have hsub : ∀ is x, x ∈ G is → x ∈ piece D (τ is.1) := by
    rintro ⟨i, s⟩ x hx
    simp only [G] at hx
    split_ifs at hx
    · exact hx
    · simp at hx
    · cases s with
      | none => simp at hx
      | some j => exact hx.1
  have huniq : ∀ is js x, x ∈ G is → x ∈ G js → is = js := by
    rintro ⟨i, s⟩ ⟨j, t⟩ x hx hy
    have hij : i = j := τ_inj ((hsub _ x hx).2.2.symm.trans (hsub _ x hy).2.2)
    subst hij
    have hxB : x ∈ Bz Z := (hsub _ x hx).1
    simp only [G] at hx hy
    by_cases hb : bad i
    · rw [if_pos hb] at hx hy
      split_ifs at hx hy with h1 h2
      · rw [h1, h2]
      · simp at hy
      · simp at hx
      · simp at hx
    · rw [if_neg hb] at hx hy
      cases s with
      | none => simp at hx
      | some a =>
        cases t with
        | none => simp at hy
        | some b =>
          have ha : IsNilpotent (x - rt a) := ⟨q, hx.2⟩
          have hb' : IsNilpotent (x - rt b) := ⟨q, hy.2⟩
          have hca : Commute (rt a) x := hxB _ (hrt a).1
          have hcb : Commute (rt b) x := hxB _ (hrt b).1
          have hab : Commute (rt b) (rt a) := hZ.1 _ (hrt b).1 _ (hrt a).1
          have hcomm : Commute (x - rt b) (x - rt a) :=
            ((Commute.refl x).sub_right hca.symm).sub_left (hcb.sub_right hab)
          have hn : IsNilpotent (rt a - rt b) := by
            have := hcomm.isNilpotent_sub hb' ha
            rwa [sub_sub_sub_cancel_left] at this
          have h0 := hred _ (Z.sub_mem (hrt a).1 (hrt b).1) hn
          rw [rt_inj (sub_eq_zero.1 h0)]
  have hclosed : ∀ is, IsClosed (G is) := by
    rintro ⟨i, s⟩
    simp only [G]
    split_ifs
    · exact (hP N q Z hZ χ D (τ i)).1
    · exact isClosed_empty
    · cases s with
      | none => exact isClosed_empty
      | some j =>
        exact (hP N q Z hZ χ D (τ i)).1.inter
          (isClosed_eq ((continuous_id.sub continuous_const).pow q) continuous_const)
  have hinvar : ∀ is, ∀ g ∈ Gz Z, ∀ x ∈ G is, g.val * x * g⁻¹.val ∈ G is := by
    rintro ⟨i, s⟩ g hg x hx
    have hP2 := (hP N q Z hZ χ D (τ i)).2.1 g hg
    simp only [G] at hx ⊢
    split_ifs at hx ⊢
    · exact hP2 x hx
    · simp at hx
    · cases s with
      | none => simp at hx
      | some j =>
        refine ⟨hP2 x hx.1, ?_⟩
        have e1 : g.val * x * g⁻¹.val - rt j = g.val * (x - rt j) * g⁻¹.val := by
          rw [mul_sub, sub_mul, ← hg (rt j) (hrt j).1, mul_assoc (rt j), Units.mul_inv, mul_one]
        rw [e1, conj_pow', hx.2, mul_zero, zero_mul]
  have hcover : ∀ x ∈ Bz Z, x.charpoly = χ → ∃ is, x ∈ G is := by
    intro x hx hc
    have hle : ∀ t, typ D x t < N + 1 := fun t =>
      Nat.lt_succ_of_le ((Matrix.rank_le_width _).trans (by simp))
    let i := e.symm fun t => ⟨typ D x t, hle t⟩
    have hxp : x ∈ piece D (τ i) :=
      ⟨hx, by rw [← hc]; exact Matrix.aeval_self_charpoly x, by funext t; simp [τ, i]⟩
    by_cases hb : bad i
    · refine ⟨(i, none), ?_⟩
      simp only [G, if_pos hb, if_true]
      exact hxp
    · rcases hD N q Z hZ χ D (τ i) x hxp with h | ⟨c, hc, hn⟩
      · exact (hb ⟨x, hxp, h⟩).elim
      · have hroot : aeval c χ = 0 := root_of_nil hZ hx hc hxp.2.1 hn
        have hmem : c ∈ hfin.toFinset := hfin.mem_toFinset.2 ⟨hc, hroot⟩
        refine ⟨(i, some (hfin.toFinset.equivFin ⟨c, hmem⟩)), ?_⟩
        have hrtc : rt (hfin.toFinset.equivFin ⟨c, hmem⟩) = c := by simp [rt]
        simp only [G, if_neg hb, Option.elim_some]
        refine ⟨hxp, ?_⟩
        rw [hrtc]
        exact hB _ (hcz c hc x hx) hn
  have hgood : ∀ is, Good Z (G is) := by
    rintro ⟨i, s⟩
    simp only [G]
    split_ifs with h1
    · obtain ⟨x₀, hx₀, hlt⟩ := h1
      exact Or.inr ⟨N, Sx D x₀, (hP N q Z hZ χ D (τ i)).2.2 x₀ hx₀, hlt, hT hF p hU N q Z hZ χ D (τ i) x₀ hx₀⟩
    · exact Or.inl ⟨0, Z.zero_mem, fun x hx => by simp at hx⟩
    · cases s with
      | none => exact Or.inl ⟨0, Z.zero_mem, fun x hx => by simp at hx⟩
      | some j => exact Or.inl ⟨rt j, (hrt j).1, fun x hx => ⟨q, hx.2⟩⟩
  let eqv := Fintype.equivFin (Fin ((N + 1) ^ D.m) × Option (Fin hfin.toFinset.card))
  refine ⟨Fintype.card (Fin ((N + 1) ^ D.m) × Option (Fin hfin.toFinset.card)), fun i => G (eqv.symm i),
    ⟨fun i => ⟨hclosed _, fun x hx => (hsub _ x hx).1, hinvar _⟩,
      fun i j hij => Set.disjoint_left.2 fun x h1 h2 => hij (eqv.symm.injective (huniq _ _ x h1 h2)),
      fun x hx hc => ?_⟩, fun i => hgood _⟩
  obtain ⟨is, his⟩ := hcover x hx hc
  exact ⟨eqv is, by simpa using his⟩

end PositivityTheory.RgUd.TP.Desc.Piece.PAsm2

end
