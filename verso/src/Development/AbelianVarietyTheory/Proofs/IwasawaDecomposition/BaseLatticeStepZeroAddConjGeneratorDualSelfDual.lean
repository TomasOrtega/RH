import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.TiedTwJSym
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoordsStatement
import Formalism.SharpRestriction.GlobalSchurBounds.Joints

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

/- English proof (translation)
Establish `hform1 : ∀ x y : Fin n → E, hform σ (1 : Matrix (Fin n) (Fin n) E) x y = ∑ i, σ (x i) * y i`. Introduce `x y`. Unfold `hform`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[Matrix.one_apply]`.

Establish `hσO : ∀ r : 𝓞 E, σ (r : E) ∈ (algebraMap (𝓞 E) E).range` using `fun r => ⟨⟨σ (r : E), map_isIntegral_int σ (RingOfIntegers.isIntegral_coe r)⟩, rfl⟩`. Apply `le_antisymm` to reduce the goal to its premises. Use `sup_le ?_ ?_` and prove the remaining obligations. Introduce `x hx`. Use `(hM x).2 fun j => ?_` and prove the remaining obligations.

Take `⟨r, hr, -⟩` from `(hL x).1 hx j`. Conclude with `⟨r, hr.symm⟩`. Rewrite using `[Submodule.ideal_span_singleton_smul]`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Simplify using `only [DistribSMul.toLinearMap_apply]`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Use `(hM _).2 fun j => ?_` and prove the remaining obligations. Distinguish the cases in `hj : j.1 + 1 = n`. Establish `hx : Pi.single j (π : E) ∈ Lb`.

Use `(hL _).2 fun i => ?_` and prove the remaining obligations. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Conclude with `⟨π, by simp, fun _ => dvd_rfl⟩`. Conclude with `⟨0, by simp [h], fun _ => dvd_zero _⟩`.

Use `hy _ hx` as an intermediate fact. Rewrite `this` using `[hform1, Finset.sum_eq_single j (by intro b _ hb; simp [hb]) (by simp)]`. Simplify `this` using `[Algebra.smul_def, hpb]`. Establish `hx : Pi.single j (1 : E) ∈ Lb`. Use `(hL _).2 fun i => ?_` and prove the remaining obligations.

Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Conclude with `⟨1, by simp, fun hi => absurd hi hj⟩`. Conclude with `⟨0, by simp [h], fun _ => dvd_zero _⟩`. Use `hy _ hx` as an intermediate fact.

Rewrite `this` using `[hform1, Finset.sum_eq_single j (by intro b _ hb; simp [hb]) (by simp)]`. Simplify using `only [Pi.single_eq_same, map_one, one_mul] at this`. Take `⟨r, hr⟩` from `this`. Conclude with `⟨pb * r, by simp [Algebra.smul_def, hr]⟩`. Consider the case `zero => simp`.

Consider the case `add y z _ _ h1 h2 => rw [smul_add]`. Conclude with `M.add_mem h1 h2`. Consider the case `smul c y _ h => rw [smul_comm]`. Conclude with `M.smul_mem c h`. Introduce `x hx`.

Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Conclude with `(le_sup_left : Lb ≤ _) ((hL x).2 fun j => j.elim0)`. Establish `hxi` using `(hM x).1 hx`. Set `l : Fin n` to `⟨n - 1, by omega⟩`. Establish `hl : l.1 + 1 = n` using `by simp [l]; omega`.

Establish `hπ : π ≠ 0`. Introduce and unpack `rfl`. Establish `hle : Submodule.span E (Lb : Set (Fin n → E)) ≤ LinearMap.ker (LinearMap.proj (R` using `E) (φ := fun _ : Fin n => E) l) := by`. Use `Submodule.span_le.2 fun z hz => ?_` and prove the remaining obligations. Take `⟨r, hr, hd⟩` from `(hL z).1 hz l`.

Establish `: r = 0` using `zero_dvd_iff.1 (hd hl)`. Simplify using `[hr, this]`. Rewrite `hle` using `[hspan]`. Use `hle (Submodule.mem_top (x := Pi.single l (1 : E)))` as an intermediate fact. Simplify using `at this`.

Establish `hpb0 : (pb : E) ≠ 0`. Rewrite using `[hpb]`. Introduce `h`. Conclude with `hπ (by simpa using (map_eq_zero σ).1 h)`. Take `⟨t, ht⟩` from `hxi l`.

Establish `hy : Pi.single l (x l / (pb : E)) ∈ dualSet σ (1 : Matrix (Fin n) (Fin n) E) Lb`. Introduce `z hz`. Rewrite using `[hform1, Finset.sum_eq_single l (by intro b _ hb; simp [hb]) (by simp)]`. Take `⟨r, hr, hd⟩` from `(hL z).1 hz l`. Take `⟨s, rfl⟩` from `hd hl`.

Take `⟨w, hw⟩` from `hσO s`. Use `⟨w * t, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hw, ht, hr, Pi.single_eq_same]`. Simplify using `only [map_mul, ← hpb]`. Rewrite using `[← ht]`.

Clear the denominators using the available nonvanishing facts. Establish `hx' : Function.update x l 0 ∈ Lb`. Use `(hL _).2 fun j => ?_` and prove the remaining obligations. Distinguish the cases in `h : j = l`. Substitute `h` using the available equality.

Conclude with `⟨0, by simp, fun _ => dvd_zero _⟩`. Take `⟨r, hr⟩` from `hxi j`. Use `⟨r, by simp [h, hr], fun hj => absurd (Fin.ext (by simp [l]; omega)) h⟩` and prove the remaining obligations. Establish `hx'' : Pi.single l (x l) ∈ Ideal.span {pb} • Submodule.span (𝓞 E) (dualSet σ (1 : Matrix (Fin n) (Fin n) E) Lb)`. Rewrite using `[Submodule.ideal_span_singleton_smul]`.

Use `⟨_, Submodule.subset_span hy, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = l`. Substitute `h` using the available equality. Simplify using `[Algebra.smul_def, mul_div_cancel₀ _ hpb0]`.

Simplify using `[h]`. Use `Submodule.mem_sup.2 ⟨_, hx', _, hx'', ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = l`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h]`.
-/
theorem base_sup_dual_eq {E : Type} [Field E] [NumberField E] (σ : E →+* E) {n : ℕ}
    (Lb M : Submodule (𝓞 E) (Fin n → E)) (π pb : 𝓞 E) (hpb : (pb : E) = σ (π : E))
    (hspan : Submodule.span E (Lb : Set (Fin n → E)) = ⊤)
    (hL : ∀ x, x ∈ Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → π ∣ r))
    (hM : ∀ x, x ∈ M ↔ ∀ j, x j ∈ (algebraMap (𝓞 E) E).range) :
    Lb ⊔ Ideal.span {pb} • Submodule.span (𝓞 E) (dualSet σ (1 : Matrix (Fin n) (Fin n) E) Lb) = M := by
  have hform1 : ∀ x y : Fin n → E, hform σ (1 : Matrix (Fin n) (Fin n) E) x y = ∑ i, σ (x i) * y i := by
    intro x y
    unfold hform
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.one_apply]
  have hσO : ∀ r : 𝓞 E, σ (r : E) ∈ (algebraMap (𝓞 E) E).range := fun r =>
    ⟨⟨σ (r : E), map_isIntegral_int σ (RingOfIntegers.isIntegral_coe r)⟩, rfl⟩
  apply le_antisymm
  · refine sup_le ?_ ?_
    · intro x hx
      refine (hM x).2 fun j => ?_
      obtain ⟨r, hr, -⟩ := (hL x).1 hx j
      exact ⟨r, hr.symm⟩
    · rw [Submodule.ideal_span_singleton_smul]
      rintro _ ⟨y, hy, rfl⟩
      simp only [DistribSMul.toLinearMap_apply]
      induction hy using Submodule.span_induction with
      | mem y hy =>
        refine (hM _).2 fun j => ?_
        by_cases hj : j.1 + 1 = n
        · have hx : Pi.single j (π : E) ∈ Lb := by
            refine (hL _).2 fun i => ?_
            by_cases h : i = j
            · subst h
              exact ⟨π, by simp, fun _ => dvd_rfl⟩
            · exact ⟨0, by simp [h], fun _ => dvd_zero _⟩
          have := hy _ hx
          rw [hform1, Finset.sum_eq_single j (by intro b _ hb; simp [hb]) (by simp)] at this
          simpa [Algebra.smul_def, hpb] using this
        · have hx : Pi.single j (1 : E) ∈ Lb := by
            refine (hL _).2 fun i => ?_
            by_cases h : i = j
            · subst h
              exact ⟨1, by simp, fun hi => absurd hi hj⟩
            · exact ⟨0, by simp [h], fun _ => dvd_zero _⟩
          have := hy _ hx
          rw [hform1, Finset.sum_eq_single j (by intro b _ hb; simp [hb]) (by simp)] at this
          simp only [Pi.single_eq_same, map_one, one_mul] at this
          obtain ⟨r, hr⟩ := this
          exact ⟨pb * r, by simp [Algebra.smul_def, hr]⟩
      | zero => simp
      | add y z _ _ h1 h2 => rw [smul_add]; exact M.add_mem h1 h2
      | smul c y _ h => rw [smul_comm]; exact M.smul_mem c h
  · intro x hx
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact (le_sup_left : Lb ≤ _) ((hL x).2 fun j => j.elim0)
    have hxi := (hM x).1 hx
    let l : Fin n := ⟨n - 1, by omega⟩
    have hl : l.1 + 1 = n := by simp [l]; omega
    have hπ : π ≠ 0 := by
      rintro rfl
      have hle : Submodule.span E (Lb : Set (Fin n → E)) ≤ LinearMap.ker (LinearMap.proj (R := E) (φ := fun _ : Fin n => E) l) := by
        refine Submodule.span_le.2 fun z hz => ?_
        obtain ⟨r, hr, hd⟩ := (hL z).1 hz l
        have : r = 0 := zero_dvd_iff.1 (hd hl)
        simp [hr, this]
      rw [hspan] at hle
      have := hle (Submodule.mem_top (x := Pi.single l (1 : E)))
      simp at this
    have hpb0 : (pb : E) ≠ 0 := by
      rw [hpb]
      intro h
      exact hπ (by simpa using (map_eq_zero σ).1 h)
    obtain ⟨t, ht⟩ := hxi l
    have hy : Pi.single l (x l / (pb : E)) ∈ dualSet σ (1 : Matrix (Fin n) (Fin n) E) Lb := by
      intro z hz
      rw [hform1, Finset.sum_eq_single l (by intro b _ hb; simp [hb]) (by simp)]
      obtain ⟨r, hr, hd⟩ := (hL z).1 hz l
      obtain ⟨s, rfl⟩ := hd hl
      obtain ⟨w, hw⟩ := hσO s
      refine ⟨w * t, ?_⟩
      rw [map_mul, hw, ht, hr, Pi.single_eq_same]
      simp only [map_mul, ← hpb]
      rw [← ht]
      field_simp
    have hx' : Function.update x l 0 ∈ Lb := by
      refine (hL _).2 fun j => ?_
      by_cases h : j = l
      · subst h
        exact ⟨0, by simp, fun _ => dvd_zero _⟩
      · obtain ⟨r, hr⟩ := hxi j
        refine ⟨r, by simp [h, hr], fun hj => absurd (Fin.ext (by simp [l]; omega)) h⟩
    have hx'' : Pi.single l (x l) ∈ Ideal.span {pb} • Submodule.span (𝓞 E) (dualSet σ (1 : Matrix (Fin n) (Fin n) E) Lb) := by
      rw [Submodule.ideal_span_singleton_smul]
      refine ⟨_, Submodule.subset_span hy, ?_⟩
      funext j
      by_cases h : j = l
      · subst h
        simp [Algebra.smul_def, mul_div_cancel₀ _ hpb0]
      · simp [h]
    refine Submodule.mem_sup.2 ⟨_, hx', _, hx'', ?_⟩
    funext j
    by_cases h : j = l
    · subst h
      simp
    · simp [h]

end GlobalTheory.Mem.Col2.TC

namespace GlobalTheory.Mem.Col2.TC

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `B X I hI hP l Z H F A hS hH hT u pb hpb`. Take `⟨-, -, -, hN⟩` from `GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hI hP l Z`. Take `⟨hgram, hl0, -⟩` from `hN 0 (Nat.zero_le _)`. Establish `hgram0 : (I.rec7 l Z).sp.gram0 = 1`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations.

Use `congrFun (congrFun hgram (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) a)) (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) b)` as an intermediate fact. Establish `e : (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) a = Fin.cast (rank_eq_first_level (I.rec7 l Z).R) b) ↔ a = b` using `by simp [Fin.ext_iff]`. Simplify using `only [Matrix.one_apply, e] at this`. Rewrite using `[Matrix.one_apply]`. Conclude with `this`.

Rewrite using `[hgram0]`. Take `⟨k, hk⟩` from `(hS u).1.ends 0 (Nat.zero_le _) (Or.inl rfl)`. Establish `hLb` using `(hH.car0 u).Lb_eq`. Establish `hπ : (A u).piU = X.piT u` using `(hT.piU u).symm.trans (hS u).1.piU`. Use `base_sup_dual_eq _ _ _ (X.piT u) pb ?_ (H.lev0 u).Lb_span ?_ ?_` and prove the remaining obligations.

Establish `e` using `congrArg (fun t : 𝓞 B.host.E => (t : B.host.E)) hπ`. Conclude with `hpb.trans ((congrArg (I.rec7 l Z).host.conj e).trans (Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj (I.rec7 l Z) _).symm)`. Introduce `x`. Establish `e1 : x ∈ (H.lev0 u).Lb ↔ reV (rank_eq_first_level (I.rec7 l Z).R) _ x ∈ ((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb`. Rewrite using `[hLb]`.

Prove the components needed by the constructor for the conclusion. Conclude with `fun h => ⟨x, h, rfl⟩`. Introduce and unpack `⟨y, hy, e⟩`. Establish `: y = x` using `(reV (rank_eq_first_level (I.rec7 l Z).R) _).injective e`. Conclude with `this ▸ hy`.

Use `e1.trans ((hk.lb () _).trans ?_)` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `h j`. Take `⟨r, hr, hd⟩` from `h (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) j)`. Conclude with `⟨r, hr, fun hj => hd (hj.trans (rank_eq_first_level _))⟩`.

Introduce `h j`. Take `⟨r, hr, hd⟩` from `h (Fin.cast (rank_eq_first_level (I.rec7 l Z).R).symm j)`. Conclude with `⟨r, hr, fun hj => hd (hj.trans (rank_eq_first_level _).symm)⟩`. Introduce `x`. Establish `e1 : (fun j => x (Fin.cast (rank_eq_first_level (I.rec7 l Z).R).symm j)) ∈ selfDualLatticeCoords (I.rec7 l Z) 0 (Nat.zero_le _) ↔ x ∈ (I.rec7 l Z).sp.crdLat0 ((I.rec7 l Z).sp.X 0).L0`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, e⟩`. Use `⟨v, hv, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Conclude with `congrFun e (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) a)`.

Introduce and unpack `⟨v, hv, e⟩`. Use `⟨v, hv, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Conclude with `congrFun e (Fin.cast (rank_eq_first_level (I.rec7 l Z).R).symm j)`. Use `e1.symm.trans ((hl0 _).trans ?_)` and prove the remaining obligations.

Conclude with `⟨fun h j => h (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) j), fun h j => h (Fin.cast (rank_eq_first_level (I.rec7 l Z).R).symm j)⟩`.
-/
theorem base_step_zero_tied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → ∀ u (pb : 𝓞 (I.rec7 l Z).host.E), (pb : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj ((A u).piU : (I.rec7 l Z).host.E) → (H.lev0 u).Lb ⊔ Ideal.span {pb} • Submodule.span (𝓞 (I.rec7 l Z).host.E) (dualSet ((I.rec7 l Z).sp.cm.sig : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (I.rec7 l Z).sp.gram0 (H.lev0 u).Lb) = (I.rec7 l Z).sp.crdLat0 ((I.rec7 l Z).sp.X 0).L0 := by
  intro B X I hI hP l Z H F A hS hH hT u pb hpb
  obtain ⟨-, -, -, hN⟩ := GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hI hP l Z
  obtain ⟨hgram, hl0, -⟩ := hN 0 (Nat.zero_le _)
  have hgram0 : (I.rec7 l Z).sp.gram0 = 1 := by
    refine Matrix.ext fun a b => ?_
    have := congrFun (congrFun hgram (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) a)) (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) b)
    have e : (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) a = Fin.cast (rank_eq_first_level (I.rec7 l Z).R) b) ↔ a = b := by simp [Fin.ext_iff]
    simp only [Matrix.one_apply, e] at this
    rw [Matrix.one_apply]
    exact this
  rw [hgram0]
  obtain ⟨k, hk⟩ := (hS u).1.ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hLb := (hH.car0 u).Lb_eq
  have hπ : (A u).piU = X.piT u := (hT.piU u).symm.trans (hS u).1.piU
  refine base_sup_dual_eq _ _ _ (X.piT u) pb ?_ (H.lev0 u).Lb_span ?_ ?_
  · have e := congrArg (fun t : 𝓞 B.host.E => (t : B.host.E)) hπ
    exact hpb.trans ((congrArg (I.rec7 l Z).host.conj e).trans (Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj (I.rec7 l Z) _).symm)
  · intro x
    have e1 : x ∈ (H.lev0 u).Lb ↔ reV (rank_eq_first_level (I.rec7 l Z).R) _ x ∈ ((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb := by
      rw [hLb]
      constructor
      · exact fun h => ⟨x, h, rfl⟩
      · rintro ⟨y, hy, e⟩
        have : y = x := (reV (rank_eq_first_level (I.rec7 l Z).R) _).injective e
        exact this ▸ hy
    refine e1.trans ((hk.lb () _).trans ?_)
    constructor
    · intro h j
      obtain ⟨r, hr, hd⟩ := h (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) j)
      exact ⟨r, hr, fun hj => hd (hj.trans (rank_eq_first_level _))⟩
    · intro h j
      obtain ⟨r, hr, hd⟩ := h (Fin.cast (rank_eq_first_level (I.rec7 l Z).R).symm j)
      exact ⟨r, hr, fun hj => hd (hj.trans (rank_eq_first_level _).symm)⟩
  · intro x
    have e1 : (fun j => x (Fin.cast (rank_eq_first_level (I.rec7 l Z).R).symm j)) ∈ selfDualLatticeCoords (I.rec7 l Z) 0 (Nat.zero_le _) ↔
        x ∈ (I.rec7 l Z).sp.crdLat0 ((I.rec7 l Z).sp.X 0).L0 := by
      constructor
      · rintro ⟨v, hv, e⟩
        refine ⟨v, hv, ?_⟩
        funext a
        exact congrFun e (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) a)
      · rintro ⟨v, hv, e⟩
        refine ⟨v, hv, ?_⟩
        funext j
        exact congrFun e (Fin.cast (rank_eq_first_level (I.rec7 l Z).R).symm j)
    refine e1.symm.trans ((hl0 _).trans ?_)
    exact ⟨fun h j => h (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) j), fun h j => h (Fin.cast (rank_eq_first_level (I.rec7 l Z).R).symm j)⟩

end GlobalTheory.Mem.Col2.TC
