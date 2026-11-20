import Formalism.LocalRingCardinality.SpanPowerMembership.EmbeddingBaseFieldCondition

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.Inhab
open scoped TensorProduct

variable (D : D7) [hL : IsEmpty D.nd.Loc] (C : TwCore D.R D.host D.what₂ D.LL0 D.nd) (I : NzIn C)
  (he : ∀ g : G0g D.nd, D.what₂.embLL ((I.eL g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)
  (E : EmbC D C)

section One

variable (M : HLat D.what₂.LL) (w : D.what₂.places.Pl) (j : ℕ) (eI : I.ix j → M.ι)

abbrev vE : (I.ix j → FractionRing (C.Ok (E.twI w) 1)) ≃ₗ[C.Ok (E.twI w) 1]
    (C.Ok (E.twI w) 1) ⊗[C.O (E.twI w)] (I.ix j → FractionRing (C.O (E.twI w))) :=
  vecE (C.O (E.twI w)) (C.Ok (E.twI w) 1) (I.ix j) (C.Ok_inj (E.twI w) 1)

def crd (x : M.V) : I.ix j → FractionRing (C.Ok (E.twI w) 1) := fun a => E.embW w (M.b.repr x (eI a))

def eMjN : M.V →+ (C.Ok (E.twI w) 1) ⊗[C.O (E.twI w)] (I.ix j → FractionRing (C.O (E.twI w))) where
  toFun x := vE D C I E w j (crd D C I E M w j eI x)
  map_zero' := by
    have : crd D C I E M w j eI 0 = 0 := funext fun a => by simp [crd]
    rw [this, map_zero]
  map_add' x y := by
    have : crd D C I E M w j eI (x + y) = crd D C I E M w j eI x + crd D C I E M w j eI y :=
      funext fun a => by simp [crd]
    rw [this, map_add]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem eMjN_apply (x : M.V) : eMjN D C I E M w j eI x = vE D C I E w j (crd D C I E M w j eI x) := rfl

/- English proof (translation)
Establish `: crd D C I E M w j eI (a • x) = r • crd D C I E M w j eI x` using `funext fun c => by show E.embW w (M.b.repr (a • x) (eI c)) = r • E.embW w (M.b.repr x (eI c))`. Rewrite using `[map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, h, Algebra.smul_def]`. Rewrite using `[eMjN_apply, this, map_smul, eMjN_apply]`.
-/
theorem eMjN_smul (a : D.what₂.LL) (r : C.Ok (E.twI w) 1) (x : M.V)
    (h : E.embW w a = algebraMap (C.Ok (E.twI w) 1) (FractionRing (C.Ok (E.twI w) 1)) r) :
    eMjN D C I E M w j eI (a • x) = r • eMjN D C I E M w j eI x := by
  have : crd D C I E M w j eI (a • x) = r • crd D C I E M w j eI x := funext fun c => by
    show E.embW w (M.b.repr (a • x) (eI c)) = r • E.embW w (M.b.repr x (eI c))
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, h, Algebra.smul_def]
  rw [eMjN_apply, this, map_smul, eMjN_apply]

/- English proof (translation)
Take `⟨r, hr⟩` from `(E.embW_w w (c : D.what₂.LL)).mp ((val_nonneg_iff D w _).mpr ((D.plEq w).valuation_le_one c))`. Conclude with `⟨r, hr.symm⟩`.
-/
theorem exists_int (c : 𝓞 D.what₂.LL) : ∃ r : C.Ok (E.twI w) 1,
    E.embW w (c : D.what₂.LL) = algebraMap (C.Ok (E.twI w) 1) (FractionRing (C.Ok (E.twI w) 1)) r := by
  obtain ⟨r, hr⟩ := (E.embW_w w (c : D.what₂.LL)).mp
    ((val_nonneg_iff D w _).mpr ((D.plEq w).valuation_le_one c))
  exact ⟨r, hr.symm⟩

variable (hb : Function.Bijective eI)

include hb in
/- English proof (translation)
Use function extensionality and compare the values at `c`. Use `show E.embW w (M.b.repr (M.b (eI a)) (eI c)) = _`. Rewrite using `[M.b.repr_self, Finsupp.single_apply, Pi.single_apply]`. Distinguish the cases in `h : c = a`. Substitute `h` using the available equality.

Rewrite using `[if_pos rfl, if_pos rfl, map_one]`. Rewrite using `[if_neg (fun h' => h (hb.1 h').symm), if_neg h, map_zero]`.
-/
theorem crd_b (a : I.ix j) : crd D C I E M w j eI (M.b (eI a)) = Pi.single a 1 := by
  funext c
  show E.embW w (M.b.repr (M.b (eI a)) (eI c)) = _
  rw [M.b.repr_self, Finsupp.single_apply, Pi.single_apply]
  by_cases h : c = a
  · subst h; rw [if_pos rfl, if_pos rfl, map_one]
  · rw [if_neg (fun h' => h (hb.1 h').symm), if_neg h, map_zero]

def sv (a : I.ix j) : (C.Ok (E.twI w) 1) ⊗[C.O (E.twI w)] (I.ix j → FractionRing (C.O (E.twI w))) :=
  vE D C I E w j (Pi.single a 1)

include hb in
/- English proof (translation)
Rewrite using `[eMjN_apply, crd_b D C I E M w j eI hb]`. Both sides reduce to the same expression.
-/
theorem eMjN_b (a : I.ix j) : eMjN D C I E M w j eI (M.b (eI a)) = sv D C I E w j a := by
  rw [eMjN_apply, crd_b D C I E M w j eI hb]; rfl

/- English proof (translation)
The claim follows from `(single_li (C.Ok (E.twI w) 1) (I.ix j) (IsFractionRing.injective _ _)).map' _ (vE D C I E w j).ker`.
-/
theorem sv_li : LinearIndependent (C.Ok (E.twI w) 1) (sv D C I E w j) :=
  (single_li (C.Ok (E.twI w) 1) (I.ix j) (IsFractionRing.injective _ _)).map' _ (vE D C I E w j).ker

include hb in
/- English proof (translation)
Set `e` to `Equiv.ofBijective eI hb`. Establish `h : (fun a => eMjN D C I E M w j eI (M.b a)) = sv D C I E w j ∘ e.symm` using `funext fun a => by`. Establish `: a = eI (e.symm a)` using `(e.apply_symm_apply a).symm`. Use `conv_lhs => rw [this]`. Conclude with `eMjN_b D C I E M w j eI hb _`.

Rewrite using `[h]`. Conclude with `(sv_li D C I E w j).comp _ e.symm.injective`.
-/
theorem eMjN_li : LinearIndependent (C.Ok (E.twI w) 1) (fun a => eMjN D C I E M w j eI (M.b a)) := by
  let e := Equiv.ofBijective eI hb
  have h : (fun a => eMjN D C I E M w j eI (M.b a)) = sv D C I E w j ∘ e.symm := funext fun a => by
    have : a = eI (e.symm a) := (e.apply_symm_apply a).symm
    conv_lhs => rw [this]
    exact eMjN_b D C I E M w j eI hb _
  rw [h]
  exact (sv_li D C I E w j).comp _ e.symm.injective

include hb in
/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite `hx` using `[SetLike.mem_coe, hM]`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨a, rfl⟩` from `hx`. Take `⟨a', rfl⟩` from `hb.2 a`. Rewrite using `[eMjN_b D C I E M w j eI hb]`. Conclude with `Submodule.subset_span ⟨a', rfl⟩`.

Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx`.

Take `⟨r, hr⟩` from `exists_int D C E w c`. Rewrite using `[← algebraMap_smul D.what₂.LL c x]`. Rewrite using `[eMjN_smul D C I E M w j eI _ r x hr]`. Conclude with `Submodule.smul_mem _ _ hx`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨a, rfl⟩`. Rewrite using `[← eMjN_b D C I E M w j eI hb]`. Use `Submodule.subset_span ⟨_, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, hM]`. Conclude with `Submodule.subset_span ⟨_, rfl⟩`.
-/
theorem eMjN_span (hM : M.L = Submodule.span (𝓞 D.what₂.LL) (Set.range M.b)) :
    Submodule.span (C.Ok (E.twI w) 1) (eMjN D C I E M w j eI '' (M.L : Set M.V)) =
      Submodule.span (C.Ok (E.twI w) 1) (Set.range (sv D C I E w j)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, hM] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨a', rfl⟩ := hb.2 a
      rw [eMjN_b D C I E M w j eI hb]
      exact Submodule.subset_span ⟨a', rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      obtain ⟨r, hr⟩ := exists_int D C E w c
      rw [← algebraMap_smul D.what₂.LL c x]
      rw [eMjN_smul D C I E M w j eI _ r x hr]
      exact Submodule.smul_mem _ _ hx
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [← eMjN_b D C I E M w j eI hb]
    refine Submodule.subset_span ⟨_, ?_, rfl⟩
    rw [SetLike.mem_coe, hM]
    exact Submodule.subset_span ⟨_, rfl⟩

/- English proof (translation)
Use `⟨Submodule.fg_span (Set.finite_range _), le_top, fun x _ => ?_⟩` and prove the remaining obligations. Take `⟨z, rfl⟩` from `(vE D C I E w j).surjective x`. Take `⟨c, hc⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors (C.Ok (E.twI w) 1)) Finset.univ z`. Use `⟨c, nonZeroDivisors.ne_zero c.2, ?_⟩` and prove the remaining obligations. Establish `h1 : (c : C.Ok (E.twI w) 1) • z ∈ LinearMap.range (TwCore.incl (C.Ok (E.twI w) 1) (FractionRing (C.Ok (E.twI w) 1)) (I.ix j))` using `(TwCore.mem_range_incl _).mpr fun y => hc y (Finset.mem_univ y)`.

Rewrite `h1` using `[TwCore.range_incl_eq_span]`. Rewrite using `[← map_smul]`. Establish `h2` using `Submodule.mem_map_of_mem (f := (vE D C I E w j).toLinearMap) h1`. Rewrite `h2` using `[Submodule.map_span, ← Set.range_comp]`. Conclude with `h2`.
-/
theorem sv_lat : NForms.IsLatIn (Submodule.span (C.Ok (E.twI w) 1) (Set.range (sv D C I E w j))) ⊤ := by
  refine ⟨Submodule.fg_span (Set.finite_range _), le_top, fun x _ => ?_⟩
  obtain ⟨z, rfl⟩ := (vE D C I E w j).surjective x
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (C.Ok (E.twI w) 1)) Finset.univ z
  refine ⟨c, nonZeroDivisors.ne_zero c.2, ?_⟩
  have h1 : (c : C.Ok (E.twI w) 1) • z ∈
      LinearMap.range (TwCore.incl (C.Ok (E.twI w) 1) (FractionRing (C.Ok (E.twI w) 1)) (I.ix j)) :=
    (TwCore.mem_range_incl _).mpr fun y => hc y (Finset.mem_univ y)
  rw [TwCore.range_incl_eq_span] at h1
  rw [← map_smul]
  have h2 := Submodule.mem_map_of_mem (f := (vE D C I E w j).toLinearMap) h1
  rw [Submodule.map_span, ← Set.range_comp] at h2
  exact h2

end One

end Formalism.BasicNotions.Examples₂.NZ
