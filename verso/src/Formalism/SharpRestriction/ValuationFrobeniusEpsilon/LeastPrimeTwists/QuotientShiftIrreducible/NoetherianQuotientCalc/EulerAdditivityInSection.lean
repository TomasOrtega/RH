import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerVanishingBelowDimension

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open IsLocalRing Filter

namespace E7

section Gr

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

def IsGrHom (G H : GMod B R k) (φ : G.M →ₗ[R] H.M) : Prop :=
  ∀ m, ∀ x ∈ G.gr m, φ x ∈ H.gr m

def IsGrHom.dsMap {G H : GMod B R k} {φ : G.M →ₗ[R] H.M} (hφ : IsGrHom G H φ) :
    (DirectSum (Deg k) fun i => G.gr i) →+ DirectSum (Deg k) fun i => H.gr i :=
  DirectSum.map fun i => ((φ.restrictScalars B).restrict (hφ i)).toAddMonoidHom

/- English proof (translation)
Proceed by induction on `a using DirectSum.induction_on with`. Consider the case `zero => simp`. Consider the case `of i x`. Rewrite using `[IsGrHom.dsMap, DirectSum.map_of, DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]`. Both sides reduce to the same expression.

Consider the case `add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]`.
-/
theorem IsGrHom.coe_dsMap {G H : GMod B R k} {φ : G.M →ₗ[R] H.M} (hφ : IsGrHom G H φ)
    (a : DirectSum (Deg k) fun i => G.gr i) :
    DirectSum.coeAddMonoidHom H.gr (hφ.dsMap a) = φ (DirectSum.coeAddMonoidHom G.gr a) := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    rw [IsGrHom.dsMap, DirectSum.map_of, DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/- English proof (translation)
Take `⟨a, rfl⟩` from `hG.2 x`. Establish `h : hφ.dsMap a = DirectSum.of (fun i => H.gr i) m ⟨_, hx⟩`. Apply `hH.1` to reduce the goal to its premises. Rewrite using `[hφ.coe_dsMap, DirectSum.coeAddMonoidHom_of]`. Establish `h2` using `congrArg (fun b => ((b m : H.gr m) : H.M)) h`.

Simplify using `only [DirectSum.of_eq_same] at h2`. Use `⟨a m, (a m).2, ?_⟩` and prove the remaining obligations. Rewrite using `[← h2, IsGrHom.dsMap, DirectSum.map_apply]`. Both sides reduce to the same expression.
-/
theorem IsGrHom.strict {G H : GMod B R k} {φ : G.M →ₗ[R] H.M} (hφ : IsGrHom G H φ)
    (hG : DirectSum.IsInternal G.gr) (hH : DirectSum.IsInternal H.gr) {m : Deg k} {x : G.M}
    (hx : φ x ∈ H.gr m) : ∃ y ∈ G.gr m, φ y = φ x := by
  obtain ⟨a, rfl⟩ := hG.2 x
  have h : hφ.dsMap a = DirectSum.of (fun i => H.gr i) m ⟨_, hx⟩ := by
    apply hH.1
    rw [hφ.coe_dsMap, DirectSum.coeAddMonoidHom_of]
  have h2 := congrArg (fun b => ((b m : H.gr m) : H.M)) h
  simp only [DirectSum.of_eq_same] at h2
  refine ⟨a m, (a m).2, ?_⟩
  rw [← h2, IsGrHom.dsMap, DirectSum.map_apply]
  rfl

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, rfl⟩`. Take `⟨a, rfl⟩` from `hG.2 x`. Proceed by induction on `a using DirectSum.induction_on with`. Consider the case `zero => simp`.

Consider the case `of i x`. Rewrite using `[DirectSum.coeAddMonoidHom_of]`. Conclude with `Submodule.subset_span ⟨⟨_, rfl⟩, i, hφ i _ x.2⟩`. Consider the case `add x y hx hy`. Rewrite using `[map_add, map_add]`.

Conclude with `Submodule.add_mem _ hx hy`. Rewrite using `[Submodule.span_le]`. Conclude with `fun x hx => hx.1`.
-/
theorem IsGrHom.range_hom {G H : GMod B R k} {φ : G.M →ₗ[R] H.M} (hφ : IsGrHom G H φ)
    (hG : DirectSum.IsInternal G.gr) : H.IsHomSub (LinearMap.range φ) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := hG.2 x
    induction a using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      rw [DirectSum.coeAddMonoidHom_of]
      exact Submodule.subset_span ⟨⟨_, rfl⟩, i, hφ i _ x.2⟩
    | add x y hx hy =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hx hy
  · rw [Submodule.span_le]
    exact fun x hx => hx.1

def sesOfExact {G' G H : GMod B R k} (f : G'.M →ₗ[R] G.M) (φ : G.M →ₗ[R] H.M)
    (hf : Function.Injective f) (hex : Function.Exact f φ)
    (hfgr : ∀ m, G'.gr m = (G.gr m).comap (f.restrictScalars B)) (hφ : IsGrHom G H φ)
    (hG : DirectSum.IsInternal G.gr) (hH : DirectSum.IsInternal H.gr) :
    SES G' G (H.sub (LinearMap.range φ)) where
  f := f
  g := φ.rangeRestrict
  inj := hf
  surj := φ.surjective_rangeRestrict
  exact y := by
    rw [← hex y]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  f_gr := hfgr
  g_gr m := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx⟩ := z.2
      have hz' : φ x ∈ H.gr m := by
        rw [hx]
        exact hz
      obtain ⟨y, hy, hyx⟩ := hφ.strict hG hH hz'
      exact ⟨y, hy, Subtype.ext (hyx.trans hx)⟩
    · rintro ⟨y, hy, rfl⟩
      exact hφ m y hy

def sesOfKer {G H : GMod B R k} (N : Submodule R G.M) (φ : G.M →ₗ[R] H.M)
    (hN : ∀ y, φ y = 0 ↔ y ∈ N) (hφ : IsGrHom G H φ)
    (hG : DirectSum.IsInternal G.gr) (hH : DirectSum.IsInternal H.gr) :
    SES (G.sub N) G (H.sub (LinearMap.range φ)) :=
  sesOfExact (G' := G.sub N) N.subtype φ N.injective_subtype
    (fun y => by
      rw [hN y]
      exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, by rintro ⟨x, rfl⟩; exact x.2⟩)
    (fun _ => rfl) hφ hG hH

/- English proof (translation)
Introduce `a ha`. Rewrite `*` using `[GMod.Ann, Module.mem_annihilator]`. Introduce `x`. Conclude with `Subtype.ext (ha x.1)`.
-/
theorem ann_le_sub (F : GMod B R k) (N : Submodule R F.M) : F.Ann ≤ (F.sub N).Ann := by
  intro a ha
  rw [GMod.Ann, Module.mem_annihilator] at *
  intro x
  exact Subtype.ext (ha x.1)

/- English proof (translation)
Introduce `a ha`. Rewrite `*` using `[GMod.Ann, Module.mem_annihilator]`. Introduce `y`. Take `⟨x, rfl⟩` from `N.mkQ_surjective y`. Conclude with `(map_smul N.mkQ a x).symm.trans ((congrArg N.mkQ (ha x)).trans (map_zero _))`.
-/
theorem ann_le_quo (F : GMod B R k) (N : Submodule R F.M) : F.Ann ≤ (F.quo N).Ann := by
  intro a ha
  rw [GMod.Ann, Module.mem_annihilator] at *
  intro y
  obtain ⟨x, rfl⟩ := N.mkQ_surjective y
  exact (map_smul N.mkQ a x).symm.trans ((congrArg N.mkQ (ha x)).trans (map_zero _))

/- English proof (translation)
Rewrite using `[secs, Ideal.span_le]`. Introduce and unpack `x ⟨d, hd⟩`. Break down `List.mem_cons.1 hd with h | h` into its components or cases. Establish `: x = σ` using `congrArg Prod.snd h`. Substitute `this` using the available equality.

Conclude with `Ideal.mem_sup_left (Ideal.subset_span rfl)`. Conclude with `Ideal.mem_sup_right (Ideal.subset_span ⟨d, h⟩)`.
-/
theorem secs_cons_le_sup (δ : Deg k) (σ : R) (ts : List (Deg k × R)) :
    secs ((δ, σ) :: ts) ≤ Ideal.span {σ} ⊔ secs ts := by
  rw [secs, Ideal.span_le]
  rintro x ⟨d, hd⟩
  rcases List.mem_cons.1 hd with h | h
  · have : x = σ := congrArg Prod.snd h
    subst this
    exact Ideal.mem_sup_left (Ideal.subset_span rfl)
  · exact Ideal.mem_sup_right (Ideal.subset_span ⟨d, h⟩)

/- English proof (translation)
Take `⟨N, hN⟩` from `h`. Use `⟨N, hN.trans (sup_le (le_sup_of_le_left hJ) ((secs_cons_le_sup δ σ ts).trans (sup_le (le_sup_of_le_left ?_) le_sup_right)))⟩` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_le_iff_mem]` and apply the resulting hypothesis.
-/
theorem admissible_tail_of_cons_mem_ideal [IsLocalRing B] (𝒜 : Deg k → Submodule B R) {δ : Deg k} {σ : R}
    {ts : List (Deg k × R)} {J J' : Ideal R} (h : admitted 𝒜 ((δ, σ) :: ts) J) (hJ : J ≤ J')
    (hσ : σ ∈ J') : admitted 𝒜 ts J' := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, hN.trans (sup_le (le_sup_of_le_left hJ) ((secs_cons_le_sup δ σ ts).trans
    (sup_le (le_sup_of_le_left ?_) le_sup_right)))⟩
  rwa [Ideal.span_singleton_le_iff_mem]

end Gr

section Maps

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
variable (F : GMod B R k) (s s' : R) (d d' : Deg k)

def phi1 : ((F.shift d).ann s' d').M →ₗ[R] (F.ann (s * s') (d + d')).M :=
  LinearMap.codRestrict (LinearMap.ker (LinearMap.lsmul R F.M (s * s')))
    (LinearMap.ker (LinearMap.lsmul R F.M s')).subtype (fun x => by
      have hx : s' • x.1 = 0 := x.2
      show (s * s') • x.1 = 0
      rw [mul_smul, hx, smul_zero])

def phi2 : (F.ann (s * s') (d + d')).M →ₗ[R] (F.ann s d).M :=
  LinearMap.codRestrict (LinearMap.ker (LinearMap.lsmul R F.M s))
    ((LinearMap.lsmul R F.M s').comp (LinearMap.ker (LinearMap.lsmul R F.M (s * s'))).subtype)
    (fun x => by
      have hx : (s * s') • x.1 = 0 := x.2
      show s • s' • x.1 = 0
      rw [← mul_smul, hx])

def phi3 : (F.ann s d).M →ₗ[R] ((F.shift d).quot s').M :=
  (LinearMap.range (LinearMap.lsmul R F.M s')).mkQ.comp
    (LinearMap.ker (LinearMap.lsmul R F.M s)).subtype

def phi4 : ((F.shift d).quot s').M →ₗ[R] (F.quot (s * s')).M :=
  Submodule.mapQ (LinearMap.range (LinearMap.lsmul R F.M s'))
    (LinearMap.range (LinearMap.lsmul R F.M (s * s'))) (LinearMap.lsmul R F.M s) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨x, mul_smul s s' x⟩)

def phi5 : (F.quot (s * s')).M →ₗ[R] (F.quot s).M :=
  Submodule.mapQ (LinearMap.range (LinearMap.lsmul R F.M (s * s')))
    (LinearMap.range (LinearMap.lsmul R F.M s)) LinearMap.id (by
      rintro _ ⟨x, rfl⟩
      exact ⟨s' • x, (mul_smul s s' x).symm⟩)

end Maps

section Main

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
variable (𝒜 : Deg k → Submodule B R) (F : GMod B R k) (s s' : R) (d d' : Deg k)

/- English proof (translation)
Introduce `x y h` and use `by have h' : x.1 = y.1 := congrArg (fun z : LinearMap.ker (LinearMap.lsmul R F.M (s * s')) => z.1) h exact Subtype.ext h'`.
-/
theorem kernel_inclusion_product_injective : Function.Injective (phi1 F s s' d d') :=
  fun x y h => by
    have h' : x.1 = y.1 :=
      congrArg (fun z : LinearMap.ker (LinearMap.lsmul R F.M (s * s')) => z.1) h
    exact Subtype.ext h'

/- English proof (translation)
Use extensionality with `x`. Use `show x.1 ∈ F.gr (m - d' - d) ↔ x.1 ∈ F.gr (m - (d + d'))`. Rewrite using `[show m - d' - d = m - (d + d') by abel]`.
-/
theorem kernel_inclusion_grading_comap (m : Deg k) : ((F.shift d).ann s' d').gr m =
    ((F.ann (s * s') (d + d')).gr m).comap ((phi1 F s s' d d').restrictScalars B) := by
  ext x
  show x.1 ∈ F.gr (m - d' - d) ↔ x.1 ∈ F.gr (m - (d + d'))
  rw [show m - d' - d = m - (d + d') by abel]

/- English proof (translation)
Introduce `y`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h' : s' • y.1 = 0` using `congrArg Subtype.val h`. Conclude with `⟨⟨y.1, h'⟩, Subtype.ext rfl⟩`.

Introduce and unpack `⟨x, rfl⟩`. Conclude with `Subtype.ext x.2`.
-/
theorem kernel_inclusion_product_exact : Function.Exact (phi1 F s s' d d') (phi2 F s s' d d') := by
  intro y
  constructor
  · intro h
    have h' : s' • y.1 = 0 := congrArg Subtype.val h
    exact ⟨⟨y.1, h'⟩, Subtype.ext rfl⟩
  · rintro ⟨x, rfl⟩
    exact Subtype.ext x.2

/- English proof (translation)
Introduce `m x hx`. Establish `hx' : x.1 ∈ F.gr (m - (d + d'))` using `hx`. Use `show s' • x.1 ∈ F.gr (m - d)`. Establish `h` using `hF.smul_mem hs' hx'`. Rewrite `h` using `[show d' + (m - (d + d')) = m - d by abel]`. Then use the resulting hypothesis.
-/
theorem product_kernel_to_kernel_isGraded (hF : F.IsGr 𝒜) (hs' : s' ∈ 𝒜 d') :
    IsGrHom (F.ann (s * s') (d + d')) (F.ann s d) (phi2 F s s' d d') := by
  intro m x hx
  have hx' : x.1 ∈ F.gr (m - (d + d')) := hx
  show s' • x.1 ∈ F.gr (m - d)
  have h := hF.smul_mem hs' hx'
  rwa [show d' + (m - (d + d')) = m - d by abel] at h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h' : y.1 ∈ LinearMap.range (LinearMap.lsmul R F.M s')` using `(Submodule.Quotient.mk_eq_zero _).1 h`. Take `⟨x, hx⟩` from `h'`. Establish `hx' : s' • x = y.1` using `hx`.

Establish `hy : s • y.1 = 0` using `y.2`. Use `⟨⟨x, ?_⟩, Subtype.ext hx'⟩` and prove the remaining obligations. Use `show (s * s') • x = 0`. Rewrite using `[mul_smul, hx', hy]`. Introduce and unpack `⟨x, rfl⟩`.

Conclude with `(Submodule.Quotient.mk_eq_zero _).2 ⟨x.1, rfl⟩`.
-/
theorem ker3 (y : (F.ann s d).M) :
    phi3 F s s' d y = 0 ↔ y ∈ LinearMap.range (phi2 F s s' d d') := by
  constructor
  · intro h
    have h' : y.1 ∈ LinearMap.range (LinearMap.lsmul R F.M s') :=
      (Submodule.Quotient.mk_eq_zero _).1 h
    obtain ⟨x, hx⟩ := h'
    have hx' : s' • x = y.1 := hx
    have hy : s • y.1 = 0 := y.2
    refine ⟨⟨x, ?_⟩, Subtype.ext hx'⟩
    show (s * s') • x = 0
    rw [mul_smul, hx', hy]
  · rintro ⟨x, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x.1, rfl⟩

/- English proof (translation)
Introduce `_ x hx` and use `⟨x.1, hx, rfl⟩`.
-/
theorem kernel_to_shift_quotient_isGraded : IsGrHom (F.ann s d) ((F.shift d).quot s') (phi3 F s s' d) :=
  fun _ x hx => ⟨x.1, hx, rfl⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨x, rfl⟩` from `(LinearMap.range (LinearMap.lsmul R F.M s')).mkQ_surjective y`. Establish `h' : s • x ∈ LinearMap.range (LinearMap.lsmul R F.M (s * s'))` using `(Submodule.Quotient.mk_eq_zero _).1 h`. Take `⟨z, hz⟩` from `h'`.

Establish `hz' : (s * s') • z = s • x` using `hz`. Use `⟨⟨x - s' • z, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show s • (x - s' • z) = 0`. Rewrite using `[smul_sub, ← mul_smul, hz', sub_self]`. Use `show (LinearMap.range (LinearMap.lsmul R F.M s')).mkQ (x - s' • z) = _`.

Rewrite using `[map_sub, sub_eq_self]`. Conclude with `(Submodule.Quotient.mk_eq_zero _).2 ⟨z, rfl⟩`. Introduce and unpack `⟨w, rfl⟩`. Establish `hw : s • w.1 = 0` using `w.2`. Use `show (LinearMap.range (LinearMap.lsmul R F.M (s * s'))).mkQ (s • w.1) = 0`.

Rewrite using `[hw, map_zero]`.
-/
theorem ker4 (y : ((F.shift d).quot s').M) :
    phi4 F s s' d y = 0 ↔ y ∈ LinearMap.range (phi3 F s s' d) := by
  constructor
  · intro h
    obtain ⟨x, rfl⟩ := (LinearMap.range (LinearMap.lsmul R F.M s')).mkQ_surjective y
    have h' : s • x ∈ LinearMap.range (LinearMap.lsmul R F.M (s * s')) :=
      (Submodule.Quotient.mk_eq_zero _).1 h
    obtain ⟨z, hz⟩ := h'
    have hz' : (s * s') • z = s • x := hz
    refine ⟨⟨x - s' • z, ?_⟩, ?_⟩
    · show s • (x - s' • z) = 0
      rw [smul_sub, ← mul_smul, hz', sub_self]
    · show (LinearMap.range (LinearMap.lsmul R F.M s')).mkQ (x - s' • z) = _
      rw [map_sub, sub_eq_self]
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨z, rfl⟩
  · rintro ⟨w, rfl⟩
    have hw : s • w.1 = 0 := w.2
    show (LinearMap.range (LinearMap.lsmul R F.M (s * s'))).mkQ (s • w.1) = 0
    rw [hw, map_zero]

/- English proof (translation)
Introduce and unpack `m _ ⟨x, hx, rfl⟩`. Establish `hx' : x ∈ F.gr (m - d)` using `hx`. Establish `h` using `hF.smul_mem hs hx'`. Rewrite `h` using `[show d + (m - d) = m by abel]`. Conclude with `⟨s • x, h, rfl⟩`.
-/
theorem quotient_to_product_quotient_isGraded (hF : F.IsGr 𝒜) (hs : s ∈ 𝒜 d) :
    IsGrHom ((F.shift d).quot s') (F.quot (s * s')) (phi4 F s s' d) := by
  rintro m _ ⟨x, hx, rfl⟩
  have hx' : x ∈ F.gr (m - d) := hx
  have h := hF.smul_mem hs hx'
  rw [show d + (m - d) = m by abel] at h
  exact ⟨s • x, h, rfl⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨x, rfl⟩` from `(LinearMap.range (LinearMap.lsmul R F.M (s * s'))).mkQ_surjective y`. Establish `h' : x ∈ LinearMap.range (LinearMap.lsmul R F.M s)` using `(Submodule.Quotient.mk_eq_zero _).1 h`. Take `⟨z, hz⟩` from `h'`.

Establish `hz' : s • z = x` using `hz`. Use `⟨(LinearMap.range (LinearMap.lsmul R F.M s')).mkQ z, ?_⟩` and prove the remaining obligations. Use `show (LinearMap.range (LinearMap.lsmul R F.M (s * s'))).mkQ (s • z) = _`. Rewrite using `[hz']`. Introduce and unpack `⟨w, rfl⟩`.

Take `⟨z, rfl⟩` from `(LinearMap.range (LinearMap.lsmul R F.M s')).mkQ_surjective w`. Conclude with `(Submodule.Quotient.mk_eq_zero _).2 ⟨z, rfl⟩`.
-/
theorem ker5 (y : (F.quot (s * s')).M) :
    phi5 F s s' y = 0 ↔ y ∈ LinearMap.range (phi4 F s s' d) := by
  constructor
  · intro h
    obtain ⟨x, rfl⟩ := (LinearMap.range (LinearMap.lsmul R F.M (s * s'))).mkQ_surjective y
    have h' : x ∈ LinearMap.range (LinearMap.lsmul R F.M s) :=
      (Submodule.Quotient.mk_eq_zero _).1 h
    obtain ⟨z, hz⟩ := h'
    have hz' : s • z = x := hz
    refine ⟨(LinearMap.range (LinearMap.lsmul R F.M s')).mkQ z, ?_⟩
    show (LinearMap.range (LinearMap.lsmul R F.M (s * s'))).mkQ (s • z) = _
    rw [hz']
  · rintro ⟨w, rfl⟩
    obtain ⟨z, rfl⟩ := (LinearMap.range (LinearMap.lsmul R F.M s')).mkQ_surjective w
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨z, rfl⟩

def ses5 : SES ((F.quot (s * s')).sub (LinearMap.range (phi4 F s s' d))) (F.quot (s * s'))
    (F.quot s) where
  f := (LinearMap.range (phi4 F s s' d)).subtype
  g := phi5 F s s'
  inj := Submodule.injective_subtype _
  surj y := by
    obtain ⟨x, rfl⟩ := (LinearMap.range (LinearMap.lsmul R F.M s)).mkQ_surjective y
    exact ⟨(LinearMap.range (LinearMap.lsmul R F.M (s * s'))).mkQ x, rfl⟩
  exact y := by
    rw [ker5 F s s' d]
    exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, by rintro ⟨x, rfl⟩; exact x.2⟩
  f_gr _ := rfl
  g_gr m := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(LinearMap.range (LinearMap.lsmul R F.M (s * s'))).mkQ x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩

/- English proof (translation)
The claim follows from `Module.mem_annihilator.2 fun x => Subtype.ext x.2`.
-/
theorem mul_mem_annihilator_product_kernel : s * s' ∈ (F.ann (s * s') (d + d')).Ann :=
  Module.mem_annihilator.2 fun x => Subtype.ext x.2

/- English proof (translation)
The claim follows from `Module.mem_annihilator.2 fun x => Subtype.ext (by have hx : s • x.1 = 0 := x.2 show (s * s') • x.1 = 0 rw [mul_comm, mul_smul, hx, smul_zero])`.
-/
theorem mul_mem_annihilator_kernel : s * s' ∈ (F.ann s d).Ann :=
  Module.mem_annihilator.2 fun x => Subtype.ext (by
    have hx : s • x.1 = 0 := x.2
    show (s * s') • x.1 = 0
    rw [mul_comm, mul_smul, hx, smul_zero])

/- English proof (translation)
The claim follows from `Module.mem_annihilator.2 fun y => by obtain ⟨x, rfl⟩ := (LinearMap.range (LinearMap.lsmul R F.M s')).mkQ_surjective y refine (Submodule.Quotient.mk_eq_zero _).2 ⟨s • x, ?_⟩ show s' • s • x = (s * s') • x rw [← mul_smul, mul_comm]`.
-/
theorem mul_mem_annihilator_shift_quotient : s * s' ∈ ((F.shift d).quot s').Ann :=
  Module.mem_annihilator.2 fun y => by
    obtain ⟨x, rfl⟩ := (LinearMap.range (LinearMap.lsmul R F.M s')).mkQ_surjective y
    refine (Submodule.Quotient.mk_eq_zero _).2 ⟨s • x, ?_⟩
    show s' • s • x = (s * s') • x
    rw [← mul_smul, mul_comm]

/- English proof (translation)
The claim follows from `Module.mem_annihilator.2 fun y => by obtain ⟨x, rfl⟩ := (LinearMap.range (LinearMap.lsmul R F.M (s * s'))).mkQ_surjective y exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩`.
-/
theorem mul_mem_annihilator_product_quotient : s * s' ∈ (F.quot (s * s')).Ann :=
  Module.mem_annihilator.2 fun y => by
    obtain ⟨x, rfl⟩ := (LinearMap.range (LinearMap.lsmul R F.M (s * s'))).mkQ_surjective y
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩

end Main

end E7

end Formalism.MainNotions.V.Pf.V2.Calc
