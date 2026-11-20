import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.DofDApply
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpSNegMulExpS
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MapDofIterate

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.ExpCong

section Abstract

variable {A k ι : Type} [CommRing A] [CommRing k] (D : ι → A → A) (c : A →+* k)

def along (w : List ι) (f : A) : A := w.foldl (fun g a => D a g) f

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem along_nil (f : A) : along D [] f = f := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem along_cons (a : ι) (w : List ι) (f : A) : along D (a :: w) f = along D w (D a f) := rfl

/- English proof (translation)
Proceed by induction on `w generalizing f g with`. Consider the case `nil => rfl`. Consider the case `cons a w ih => rw [along_cons, along_cons, along_cons, hadd, ih]`.
-/
theorem along_add (hadd : ∀ a f g, D a (f + g) = D a f + D a g) (w : List ι) (f g : A) :
    along D w (f + g) = along D w f + along D w g := by
  induction w generalizing f g with
  | nil => rfl
  | cons a w ih => rw [along_cons, along_cons, along_cons, hadd, ih]

/- English proof (translation)
Proceed by induction on `w generalizing f g with`. Consider the case `nil`. Rewrite using `[along_nil, map_mul]`. Conclude with `hSJ _ (hf [] (List.Sublist.refl _)) _ (hg [] (List.Sublist.refl _))`. Consider the case `cons a w ih`.

Rewrite using `[along_cons, hmul, along_add D hadd, map_add, mul_comm g]`. Use `J.add_mem (ih _ _ ?_ ?_) (ih _ _ ?_ ?_)` and prove the remaining obligations. Conclude with `fun v hv => hf v (hv.cons a)`. Conclude with `fun v hv => hg (a :: v) (hv.cons_cons a)`. Conclude with `fun v hv => hf (a :: v) (hv.cons_cons a)`.

Conclude with `fun v hv => hg v (hv.cons a)`.
-/
theorem along_mul_mem (hadd : ∀ a f g, D a (f + g) = D a f + D a g)
    (hmul : ∀ a f g, D a (f * g) = f * D a g + g * D a f) (S : Set k) (J : AddSubgroup k)
    (hSJ : ∀ s ∈ S, ∀ j ∈ J, s * j ∈ J) (w : List ι) (f g : A)
    (hf : ∀ v, v.Sublist w → c (along D v f) ∈ S) (hg : ∀ v, v.Sublist w → c (along D v g) ∈ J) :
    c (along D w (f * g)) ∈ J := by
  induction w generalizing f g with
  | nil =>
    rw [along_nil, map_mul]
    exact hSJ _ (hf [] (List.Sublist.refl _)) _ (hg [] (List.Sublist.refl _))
  | cons a w ih =>
    rw [along_cons, hmul, along_add D hadd, map_add, mul_comm g]
    refine J.add_mem (ih _ _ ?_ ?_) (ih _ _ ?_ ?_)
    · exact fun v hv => hf v (hv.cons a)
    · exact fun v hv => hg (a :: v) (hv.cons_cons a)
    · exact fun v hv => hf (a :: v) (hv.cons_cons a)
    · exact fun v hv => hg v (hv.cons a)

/- English proof (translation)
Proceed by induction on `w generalizing f with`. Consider the case `nil`. Rewrite using `[along_nil, along_nil, map_mul, hE1, mul_one, sub_self]`. Conclude with `J.zero_mem`. Consider the case `cons a w ih`.

Establish `hφ' : ∀ v, v.Sublist w → c (along D v φ) ∈ J` using `fun v hv => hφ v (hv.cons a)`. Establish `h1 : ∀ v, v.Sublist w → c (along D v (f * D a φ)) ∈ J` using `fun v hv => along_mul_mem D c hadd hmul S J hSJ v f (D a φ) (fun v' hv' => hf v' ((hv'.trans hv).cons a)) (fun v' hv' => hφ (a :: v') ((hv'.trans hv).cons_cons a))`. Establish `h2` using `ih (f * D a φ) (fun v hv => hJS _ (h1 v hv)) hφ'`. Establish `h3` using `ih (D a f) (fun v hv => hf (a :: v) (hv.cons_cons a)) hφ'`. Establish `h4` using `J.add_mem (J.add_mem h2 (h1 w (List.Sublist.refl _))) h3`.

Rewrite using `[along_cons, along_cons, hmul, hE, along_add D hadd, map_add, show f * (E * D a φ) = f * D a φ * E by ring, mul_comm E]`. Use `h4 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem along_mul_exp (hadd : ∀ a f g, D a (f + g) = D a f + D a g)
    (hmul : ∀ a f g, D a (f * g) = f * D a g + g * D a f) (S : Set k) (J : AddSubgroup k)
    (hSJ : ∀ s ∈ S, ∀ j ∈ J, s * j ∈ J) (hJS : ∀ j ∈ J, j ∈ S) (E φ : A) (hE : ∀ a, D a E = E * D a φ)
    (hE1 : c E = 1) (w : List ι) (f : A)
    (hf : ∀ v, v.Sublist w → c (along D v f) ∈ S) (hφ : ∀ v, v.Sublist w → c (along D v φ) ∈ J) :
    c (along D w (f * E)) - c (along D w f) ∈ J := by
  induction w generalizing f with
  | nil =>
    rw [along_nil, along_nil, map_mul, hE1, mul_one, sub_self]
    exact J.zero_mem
  | cons a w ih =>
    have hφ' : ∀ v, v.Sublist w → c (along D v φ) ∈ J := fun v hv => hφ v (hv.cons a)
    have h1 : ∀ v, v.Sublist w → c (along D v (f * D a φ)) ∈ J := fun v hv =>
      along_mul_mem D c hadd hmul S J hSJ v f (D a φ)
        (fun v' hv' => hf v' ((hv'.trans hv).cons a))
        (fun v' hv' => hφ (a :: v') ((hv'.trans hv).cons_cons a))
    have h2 := ih (f * D a φ) (fun v hv => hJS _ (h1 v hv)) hφ'
    have h3 := ih (D a f) (fun v hv => hf (a :: v) (hv.cons_cons a)) hφ'
    have h4 := J.add_mem (J.add_mem h2 (h1 w (List.Sublist.refl _))) h3
    rw [along_cons, along_cons, hmul, hE, along_add D hadd, map_add,
      show f * (E * D a φ) = f * D a φ * E by ring, mul_comm E]
    convert h4 using 1
    ring

def grouped (L : List ι) (m : ι → ℕ) : List ι := L.flatMap fun l => List.replicate (m l) l

/- English proof (translation)
Simplify using `[grouped]`.
-/
theorem grouped_cons (a : ι) (L : List ι) (m : ι → ℕ) :
    grouped (a :: L) m = List.replicate (m a) a ++ grouped L m := by
  simp [grouped]

/- English proof (translation)
Proceed by induction on `L generalizing v with`. Consider the case `nil => exact ⟨m, by simpa [grouped] using hv⟩`. Consider the case `cons a L ih`. Rewrite `hv` using `[grouped_cons, List.sublist_append_iff]`. Take `⟨v₁, v₂, rfl, h₁, h₂⟩` from `hv`.

Take `⟨n, -, rfl⟩` from `List.sublist_replicate_iff.1 h₁`. Rewrite `hL` using `[List.nodup_cons]`. Take `⟨m', rfl⟩` from `ih hL.2 v₂ h₂`. Use `⟨Function.update m' a n, ?_⟩` and prove the remaining obligations. Rewrite using `[grouped_cons, Function.update_self]`.

Use `congr 1`. Unfold `grouped`. Use `List.flatMap_congr fun l hl => ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne]`. Introduce and unpack `rfl`.

Conclude with `hL.1 hl`.
-/
theorem exists_grouped_of_sublist {L : List ι} (hL : L.Nodup) (m : ι → ℕ) (v : List ι)
    (hv : v.Sublist (grouped L m)) : ∃ m' : ι → ℕ, v = grouped L m' := by
  classical
  induction L generalizing v with
  | nil => exact ⟨m, by simpa [grouped] using hv⟩
  | cons a L ih =>
    rw [grouped_cons, List.sublist_append_iff] at hv
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := hv
    obtain ⟨n, -, rfl⟩ := List.sublist_replicate_iff.1 h₁
    rw [List.nodup_cons] at hL
    obtain ⟨m', rfl⟩ := ih hL.2 v₂ h₂
    refine ⟨Function.update m' a n, ?_⟩
    rw [grouped_cons, Function.update_self]
    congr 1
    unfold grouped
    refine List.flatMap_congr fun l hl => ?_
    rw [Function.update_of_ne]
    rintro rfl
    exact hL.1 hl

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rfl`. Consider the case `succ n ih => rw [List.replicate_succ, List.foldr_cons, ih, Function.iterate_succ_apply']`.
-/
theorem foldr_replicate (a : ι) (n : ℕ) (g : A) :
    (List.replicate n a).foldr (fun a g => D a g) g = (D a)^[n] g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.foldr_cons, ih, Function.iterate_succ_apply']

/- English proof (translation)
Unfold `along`. Rewrite using `[List.foldl_reverse]`. Proceed by induction on `L with`. Consider the case `nil => rfl`. Consider the case `cons a L ih => rw [grouped_cons, List.foldr_append, ih, foldr_replicate, List.foldr_cons]`.
-/
theorem along_reverse_grouped (L : List ι) (m : ι → ℕ) (f : A) :
    along D (grouped L m).reverse f = L.foldr (fun l g => (D l)^[m l] g) f := by
  unfold along
  rw [List.foldl_reverse]
  induction L with
  | nil => rfl
  | cons a L ih => rw [grouped_cons, List.foldr_append, ih, foldr_replicate, List.foldr_cons]

end Abstract

variable {k : Type} [CommRing k] {d : ℕ} (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)

/- English proof (translation)
The claim follows from `(along_reverse_grouped _ _ _ _).symm`.
-/
theorem dmonOf_eq_along (m : ι →₀ ℕ) (f : PS k 1 d) :
    DmonOf F u m f =
      along (fun l => Dof F (u l)) (grouped (Finset.univ : Finset ι).toList m).reverse f :=
  (along_reverse_grouped _ _ _ _).symm

/- English proof (translation)
Take `⟨m', hm'⟩` from `exists_grouped_of_sublist (Finset.nodup_toList _) m v.reverse (by simpa using hv.reverse)`. Use `⟨Finsupp.equivFunOnFinite.symm m', fun f => ?_⟩` and prove the remaining obligations. Rewrite using `[dmonOf_eq_along, Finsupp.coe_equivFunOnFinite_symm, ← hm', List.reverse_reverse]`.
-/
theorem exists_along_eq_dmonOf (m : ι →₀ ℕ) (v : List ι)
    (hv : v.Sublist (grouped (Finset.univ : Finset ι).toList m).reverse) :
    ∃ m' : ι →₀ ℕ, ∀ f : PS k 1 d, along (fun l => Dof F (u l)) v f = DmonOf F u m' f := by
  obtain ⟨m', hm'⟩ := exists_grouped_of_sublist (Finset.nodup_toList _) m v.reverse
    (by simpa using hv.reverse)
  refine ⟨Finsupp.equivFunOnFinite.symm m', fun f => ?_⟩
  rw [dmonOf_eq_along, Finsupp.coe_equivFunOnFinite_symm, ← hm', List.reverse_reverse]

end GlobalTheory.ExpCong

namespace GlobalTheory

/- English proof (translation)
Introduce `R _ d k _ _ _ F I ι _ u φ hφ0 hφ f m`. Use `set F' : Fin d → PS k 2 d := fun i => MvPowerSeries.map (algebraMap R k) (F i) with hF'`. Use `set u' : ι → Fin d → k := fun l i => algebraMap R k (u l i) with hu'`. Establish `hmap : ∀ m' : ι →₀ ℕ, constantCoeff (DmonOf F' u' m' (FB.toK k f)) = algebraMap R k (constantCoeff (DmonOf F u m' f))` using `fun m' => by`. Rewrite using `[hF', hu', FB.toK, ← map_dmonOf, constantCoeff_map]`.

Establish `key` using `ExpCong.along_mul_exp (fun l => Dof F' (u' l)) (constantCoeff : PS k 1 d →+* k) (fun a => GE.dof_add F' (u' a)) (fun a => GE.dof_mul F' (u' a)) (Set.range (algebraMap R k)) (I.toAddSubgroup.map (algebraMap R k).toAddMonoidHom) (by`. Introduce and unpack `_ ⟨s, rfl⟩ _ ⟨j, hj, rfl⟩`. Conclude with `⟨s * j, I.mul_mem_left s hj, map_mul (algebraMap R k) s j⟩)`. Use the proof step `(by`. Introduce and unpack `_ ⟨j, -, rfl⟩`.

Conclude with `⟨j, rfl⟩)`. Use the proof step `(FB.expS k φ) φ (fun a => NablaExpConj.Dof_expS k F' (u' a) hφ0) (WickVanishing.constantCoeff_exp hφ0)`. Use the proof step `(ExpCong.grouped (Finset.univ : Finset ι).toList m).reverse (FB.toK k f)`. Use the proof step `(fun v hv => by`. Take `⟨m', hm'⟩` from `ExpCong.exists_along_eq_dmonOf F' u' m v hv`.

Conclude with `⟨_, by rw [hm', hmap]⟩)`. Use the proof step `(fun v hv => by`. Take `⟨m', hm'⟩` from `ExpCong.exists_along_eq_dmonOf F' u' m v hv`. Take `⟨r, hr, e⟩` from `hφ m'`. Conclude with `⟨r, hr, by rw [hm', e]; rfl⟩)`.

Rewrite `key` using `[← ExpCong.dmonOf_eq_along, ← ExpCong.dmonOf_eq_along, hmap]`. Take `⟨r, hr, e⟩` from `key`. Use `⟨r, hr, ?_⟩` and prove the remaining obligations. Establish `e' : algebraMap R k r = _` using `e`. Rewrite using `[map_add, e']`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem dmonOf_mul_expS_congr : ∀ (R : Type) [CommRing R] (d : ℕ) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (F : Fin d → PS R 2 d) (I : Ideal R) (ι : Type) [Fintype ι] (u : ι → Fin d → R) (φ : PS k 1 d), constantCoeff φ = 0 → (∀ m : ι →₀ ℕ, ∃ r ∈ I, constantCoeff (DmonOf (fun i => MvPowerSeries.map (algebraMap R k) (F i)) (fun l i => algebraMap R k (u l i)) m φ) = algebraMap R k r) → ∀ (f : PS R 1 d) (m : ι →₀ ℕ), ∃ r ∈ I, constantCoeff (DmonOf (fun i => MvPowerSeries.map (algebraMap R k) (F i)) (fun l i => algebraMap R k (u l i)) m (FB.toK k f * FB.expS k φ)) = algebraMap R k (constantCoeff (DmonOf F u m f) + r) := by
  intro R _ d k _ _ _ F I ι _ u φ hφ0 hφ f m
  set F' : Fin d → PS k 2 d := fun i => MvPowerSeries.map (algebraMap R k) (F i) with hF'
  set u' : ι → Fin d → k := fun l i => algebraMap R k (u l i) with hu'
  have hmap : ∀ m' : ι →₀ ℕ, constantCoeff (DmonOf F' u' m' (FB.toK k f)) =
      algebraMap R k (constantCoeff (DmonOf F u m' f)) := fun m' => by
    rw [hF', hu', FB.toK, ← map_dmonOf, constantCoeff_map]
  have key := ExpCong.along_mul_exp (fun l => Dof F' (u' l)) (constantCoeff : PS k 1 d →+* k)
    (fun a => GE.dof_add F' (u' a)) (fun a => GE.dof_mul F' (u' a)) (Set.range (algebraMap R k))
    (I.toAddSubgroup.map (algebraMap R k).toAddMonoidHom)
    (by
      rintro _ ⟨s, rfl⟩ _ ⟨j, hj, rfl⟩
      exact ⟨s * j, I.mul_mem_left s hj, map_mul (algebraMap R k) s j⟩)
    (by
      rintro _ ⟨j, -, rfl⟩
      exact ⟨j, rfl⟩)
    (FB.expS k φ) φ (fun a => NablaExpConj.Dof_expS k F' (u' a) hφ0) (WickVanishing.constantCoeff_exp hφ0)
    (ExpCong.grouped (Finset.univ : Finset ι).toList m).reverse (FB.toK k f)
    (fun v hv => by
      obtain ⟨m', hm'⟩ := ExpCong.exists_along_eq_dmonOf F' u' m v hv
      exact ⟨_, by rw [hm', hmap]⟩)
    (fun v hv => by
      obtain ⟨m', hm'⟩ := ExpCong.exists_along_eq_dmonOf F' u' m v hv
      obtain ⟨r, hr, e⟩ := hφ m'
      exact ⟨r, hr, by rw [hm', e]; rfl⟩)
  rw [← ExpCong.dmonOf_eq_along, ← ExpCong.dmonOf_eq_along, hmap] at key
  obtain ⟨r, hr, e⟩ := key
  refine ⟨r, hr, ?_⟩
  have e' : algebraMap R k r = _ := e
  rw [map_add, e']
  ring

end GlobalTheory
