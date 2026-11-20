import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCoprimeZpow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPELPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelStructureDescendsFieldExtensionStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.OActSpreadFromDenseFibresAbelianSchemeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdjointEndomorphismsCubeLBOfDenseFibresStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoCubeGraphOfDenseFibresStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionIsometryPrimitiveRootBijectiveModNStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TateIsometryOfFiniteLevelIsometriesStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DeterminantConditionSpreadsOfDensePointsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelIsometryOfDenseGeometricPointsStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PELFamily

section Pairing

variable {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) {T : Over S}

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => rwa [zero_add, pow_one, pow_one]`. Consider the case `succ m ih`. Rewrite using `[pow_succ x, pow_succ c]`. Conclude with `(hW S P n T).2.1 _ _ _ _ _ ih h`.
-/
theorem weilIs_pow_left (hW : Out.WeilSt) {n : ℕ} {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs P.A P.L n x y c) (m : ℕ) : Out.WeilIs P.A P.L n (x ^ (m + 1)) y (c ^ (m + 1)) := by
  induction m with
  | zero => rwa [zero_add, pow_one, pow_one]
  | succ m ih =>
    rw [pow_succ x, pow_succ c]
    exact (hW S P n T).2.1 _ _ _ _ _ ih h

/- English proof (translation)
Take `⟨m, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hm.ne'`. Establish `h₁` using `CommPairing.weilIs_symm P.isLB (weilIs_pow_left P hW (CommPairing.weilIs_symm P.isLB h) m)`. Rewrite `h₁` using `[inv_pow, inv_inv, Nat.cast_mul]`. Conclude with `((hW S P n T).2.2.2 _ x _ _ hu hx (by rw [← pow_mul, mul_comm, hy])).1 h₁`.
-/
theorem weilIs_lower (hW : Out.WeilSt) {n m : ℕ} (hm : 0 < m) (hu : IsUnit ((n * m : ℕ) : Γ(T.left, ⊤)))
    {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ} (hx : x ^ (n * m) = 1) (hy : y ^ (n * m) = 1)
    (h : Out.WeilIs P.A P.L ((n * m : ℕ) : ℤ) x y c) : Out.WeilIs P.A P.L n (x ^ m) (y ^ m) (c ^ m) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have h₁ := CommPairing.weilIs_symm P.isLB (weilIs_pow_left P hW (CommPairing.weilIs_symm P.isLB h) m)
  rw [inv_pow, inv_inv, Nat.cast_mul] at h₁
  exact ((hW S P n T).2.2.2 _ x _ _ hu hx (by rw [← pow_mul, mul_comm, hy])).1 h₁

/- English proof (translation)
Establish `h₁` using `(hW S P n _).2.1 _ _ _ _ _ h h`. Rewrite `h₁` using `[_root_.mul_one]`. Establish `e : unitOn (c * c) = unitOn c * unitOn c` using `map_mul _ _ _`. Conclude with `mul_eq_left.1 (weilIs_unique_fieldPoint S P.A P.L P.isLB K x n 1 y _ _ (e ▸ h₁) h)`.
-/
theorem eq_one_of_weilIs_one {K : Type} [Field K] (hW : Out.WeilSt) {x : Sp K ⟶ S} {n : ℕ}
    {y : Over.mk x ⟶ P.A} {c : Kˣ} (h : Out.WeilIs P.A P.L n 1 y (unitOn c)) : c = 1 := by
  have h₁ := (hW S P n _).2.1 _ _ _ _ _ h h
  rw [_root_.mul_one] at h₁
  have e : unitOn (c * c) = unitOn c * unitOn c := map_mul _ _ _
  exact mul_eq_left.1 (weilIs_unique_fieldPoint S P.A P.L P.isLB K x n 1 y _ _ (e ▸ h₁) h)

end Pairing

/- English proof (translation)
Establish `h₁ : LBIso (lbPow L 1) (M.pull (𝟙 A : A ⟶ A).left)` using `LBIso.trans (DVR.linComb_isLB _ hL _ _) hL (pull_isLB hM _) (lbIso_lbPow_one hL) h`. Use `(weilIs_along_hom hG S A A (𝟙 A) L M 1 n T x y c c hA hA hL hM inferInstance h₁ (by rwa [Category.comp_id, Category.comp_id])).1` as an intermediate fact. Rewrite `this` using `[Nat.cast_one, _root_.mul_one]`. Then use the resulting hypothesis.
-/
theorem weilIs_of_lbIso (hG : Out.GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L M : LB A.left} (hL : L.IsLB) (hM : M.IsLB) (h : LBIso L (M.pull (𝟙 A : A ⟶ A).left)) {n : ℤ} {T : Over S}
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (hw : Out.WeilIs A M n x y c) : Out.WeilIs A L n x y c := by
  have h₁ : LBIso (lbPow L 1) (M.pull (𝟙 A : A ⟶ A).left) :=
    LBIso.trans (DVR.linComb_isLB _ hL _ _) hL (pull_isLB hM _) (lbIso_lbPow_one hL) h
  have := (weilIs_along_hom hG S A A (𝟙 A) L M 1 n T x y c c hA hA hL hM inferInstance h₁
    (by rwa [Category.comp_id, Category.comp_id])).1
  rwa [Nat.cast_one, _root_.mul_one] at this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {g k : ℕ} {J : Type}
  {a : J → 𝓞 E} {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La} {o : Type} [CommRing o] {b : TBase o k} {em : o →+* ℂ} {ρ : o}
  {S : Scheme.{0}} {s : S ⟶ Sp o}

/- English proof (translation)
Take `⟨K, _, x, hx, K₀, _, β, i, j, t₀, tx, tc, hj, hs, m₁, m₂, m₃, τ, hτ⟩` from `hp`. Take `⟨τ₀, h₀⟩` from `GlobalTheory.T.pelStructure_descends_field_extension hL E H D g k J a bas o b ρ K₀ ℂ j β _ t₀ tc τ hcl (by rw [← hj]; exact Spec.map_comp _ _) m₃ hτ`. Take `⟨τ', h'⟩` from `PELPull.isPEL_pull E H D g k J a bas o b ρ _ _ _ _ _ t₀ tx τ₀ hs.symm m₂ h₀`. Establish `: CharZero K₀` using `j.charZero`. Conclude with `⟨K, inferInstance, (i.charZero_iff i.injective).1 inferInstance, x, tx, τ', hx, m₁, h'⟩`.
-/
theorem exists_fibre (hL : Out.Laws) (hcl : Subring.closure (Set.range a) = ⊤) {t : TObj g k J b s} {p : S}
    (hp : p ∈ fromSet em (PELClass (b := b) D a bas ρ em) t) :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K) (x : Sp K ⟶ S) (tx : TObj g k J b (x ≫ s)) (τ : SAB H (Sp K)),
      p ∈ Set.range x ∧ TMap tx t x ∧ IsPEL D a bas ρ tx τ := by
  obtain ⟨K, _, x, hx, K₀, _, β, i, j, t₀, tx, tc, hj, hs, m₁, m₂, m₃, τ, hτ⟩ := hp
  obtain ⟨τ₀, h₀⟩ := GlobalTheory.T.pelStructure_descends_field_extension hL E H D g k J a bas o b ρ K₀ ℂ j β _ t₀ tc τ hcl
    (by rw [← hj]; exact Spec.map_comp _ _) m₃ hτ
  obtain ⟨τ', h'⟩ := PELPull.isPEL_pull E H D g k J a bas o b ρ _ _ _ _ _ t₀ tx τ₀ hs.symm m₂ h₀
  have : CharZero K₀ := j.charZero
  exact ⟨K, inferInstance, (i.charZero_iff i.injective).1 inferInstance, x, tx, τ', hx, m₁, h'⟩

/- English proof (translation)
Take `⟨K, _, _, x, tx, τ, hx, ⟨ψ, hψ, hψL, hpt, hact⟩, φ, hφ, hφL, hφa, hgeom⟩` from `exists_fibre hL hcl hp`. Use `⟨K, inferInstance, inferInstance, x, τ, φ.hom.left ≫ ψ, hx, ((isGrpPullback_of_iso φ).comp hψ).congr (Category.id_comp x) rfl, hφL.trans τ.PP.isLB (pull_isLB tx.isLB _) (pull_isLB t.isLB _) (PELPull.lbIso_pull hψL _ rfl), fun j => ?_, fun Ω _ _ _ y β hy => ?_⟩` and prove the remaining obligations. Establish `h₁ : (τ.act.act (a j)).left ≫ φ.hom.left = φ.hom.left ≫ (tx.act j).left` using `congrArg (fun z => z.left) (hφa j)`. Rewrite using `[← Category.assoc, h₁, Category.assoc, hact, Category.assoc]`. Take `⟨hdet, I, hI, hA⟩` from `hgeom Ω y β hy`.

Use `⟨hdet, I, hI, fun i => ?_⟩` and prove the remaining obligations. Establish `h₁ : (I.ev k (bas (Pi.single i 1))).left ≫ φ.hom.left = y ≫ (tx.pt i).left` using `congrArg (fun z => z.left) (hA i)`. Rewrite using `[← Category.assoc, h₁, Category.assoc, hpt, Category.assoc]`.
-/
theorem exists_fibre_map (hL : Out.Laws) (hcl : Subring.closure (Set.range a) = ⊤) {t : TObj g k J b s} {p : S}
    (hp : p ∈ fromSet em (PELClass (b := b) D a bas ρ em) t) :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K) (x : Sp K ⟶ S) (τ : SAB H (Sp K)) (ψ : τ.G.left ⟶ t.A.left),
      p ∈ Set.range x ∧ IsGrpPullback τ.G t.A x ψ ∧ LBIso τ.PP.L (t.L.pull ψ) ∧
      (∀ j, (τ.act.act (a j)).left ≫ ψ = ψ ≫ (t.act j).left) ∧
      ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (y : Sp Ω ⟶ Sp K) (β : o →+* Ω), y ≫ x ≫ s = spMap β →
        DetCond D τ.act y (β ρ) ∧ ∃ I : TateIso D Ω (Over.mk y ⟶ τ.G) (fun c z => z ≫ τ.act.act c)
            (fun n z z' c => Out.WeilIs τ.G τ.PP.L n z z' (unitOn c)),
          (I.ζ k : Ω) = β b.ζ ∧ ∀ i, (I.ev k (bas (Pi.single i 1))).left ≫ ψ = (y ≫ x) ≫ (t.pt i).left := by
  obtain ⟨K, _, _, x, tx, τ, hx, ⟨ψ, hψ, hψL, hpt, hact⟩, φ, hφ, hφL, hφa, hgeom⟩ := exists_fibre hL hcl hp
  refine ⟨K, inferInstance, inferInstance, x, τ, φ.hom.left ≫ ψ, hx,
    ((isGrpPullback_of_iso φ).comp hψ).congr (Category.id_comp x) rfl,
    hφL.trans τ.PP.isLB (pull_isLB tx.isLB _) (pull_isLB t.isLB _) (PELPull.lbIso_pull hψL _ rfl),
    fun j => ?_, fun Ω _ _ _ y β hy => ?_⟩
  · have h₁ : (τ.act.act (a j)).left ≫ φ.hom.left = φ.hom.left ≫ (tx.act j).left :=
      congrArg (fun z => z.left) (hφa j)
    rw [← Category.assoc, h₁, Category.assoc, hact, Category.assoc]
  · obtain ⟨hdet, I, hI, hA⟩ := hgeom Ω y β hy
    refine ⟨hdet, I, hI, fun i => ?_⟩
    have h₁ : (I.ev k (bas (Pi.single i 1))).left ≫ φ.hom.left = y ≫ (tx.pt i).left :=
      congrArg (fun z => z.left) (hA i)
    rw [← Category.assoc, h₁, Category.assoc, hpt, Category.assoc]

/- English proof (translation)
Use `t.ab.comm` as an intermediate fact. Take `⟨K, _, _, x, τ, ψ, ⟨q, hq⟩, hψ, hψL, hact, hgeom⟩` from `exists_fibre_map hL hcl hp`. Establish `hc` using `hr _ x τ.G ψ τ.act hψ hact`. Set `y : Sp (AlgebraicClosure K) ⟶ Sp K` to `spMap (algebraMap K (AlgebraicClosure K))`. Take `⟨β, hβ⟩ : ∃ β : o →+* AlgebraicClosure K, y ≫ x ≫ s = spMap β` from `⟨(Spec.preimage (y ≫ x ≫ s)).hom, (Spec.map_preimage _).symm⟩`.

Take `⟨hdet, I, hI, hA⟩` from `hgeom _ y β hβ`. Use `⟨AlgebraicClosure K, inferInstance, inferInstance, inferInstance, y ≫ x, β, ⟨(default : PrimeSpectrum (AlgebraicClosure K)), ?_⟩, (Category.assoc _ _ _).trans hβ, fun σ => ?_, ObjPull.tateMove (ObjPull.pushEquiv hψ (Over.mk y)).symm (fun c z => ?_) (fun n z z' c hz => ?_) I, hI, …` and prove the remaining obligations. Conclude with `(Scheme.Hom.comp_apply y x _).trans ((congrArg x (Subsingleton.elim (α := PrimeSpectrum K) _ _)).trans hq)`. Rewrite using `[← LiePull.lieMult_pull _ _ _ t.A τ.G x ψ r τ.act hψ hc _ y σ, ← LiePull.lieMult_pull _ _ _ t.A τ.G x ψ r τ.act hψ hc _ y σ]`. Conclude with `hdet σ`.

Take `⟨z, rfl⟩` from `(ObjPull.pushEquiv hψ (Over.mk y)).surjective z`. Rewrite using `[MulEquiv.symm_apply_eq, MulEquiv.symm_apply_apply]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `show (z.left ≫ _) ≫ _ = (z.left ≫ _) ≫ _`. Rewrite using `[Category.assoc, ← hc, Category.assoc]`.

Conclude with `(weilIs_iff_of_isGrpPullback_comm _ _ t.A τ.G x ψ t.L τ.PP.L t.isLB τ.PP.isLB hψ hψL (Over.mk y) n _ _ z z' _ (ObjPull.pushEquiv_symm_left hψ (Over.mk y) z).symm (ObjPull.pushEquiv_symm_left hψ (Over.mk y) z').symm).1 hz`.
-/
theorem exists_geom (hL : Out.Laws) (hcl : Subring.closure (Set.range a) = ⊤) {t : TObj g k J b s}
    (r : OAct (𝓞 E) t.A)
    (hr : ∀ (T : Scheme.{0}) (x : T ⟶ S) (G : Over T) [GrpObj G] (φ : G.left ⟶ t.A.left) (act : OAct (𝓞 E) G),
      IsGrpPullback G t.A x φ → (∀ j, (act.act (a j)).left ≫ φ = φ ≫ (t.act j).left) →
      ∀ c, (act.act c).left ≫ φ = φ ≫ (r.act c).left) {p : S}
    (hp : p ∈ fromSet em (PELClass (b := b) D a bas ρ em) t) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ S) (β : o →+* K),
      p ∈ Set.range x ∧ x ≫ s = spMap β ∧ DetCond D r x (β ρ) ∧
      ∃ I : TateIso D K (Over.mk x ⟶ t.A) (fun c z => z ≫ r.act c)
          (fun n z z' c => Out.WeilIs t.A t.L n z z' (unitOn c)),
        (I.ζ k : K) = β b.ζ ∧ ∀ i, I.ev k (bas (Pi.single i 1)) =
          (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ t.pt i := by
  have := t.ab.comm
  obtain ⟨K, _, _, x, τ, ψ, ⟨q, hq⟩, hψ, hψL, hact, hgeom⟩ := exists_fibre_map hL hcl hp
  have hc := hr _ x τ.G ψ τ.act hψ hact
  let y : Sp (AlgebraicClosure K) ⟶ Sp K := spMap (algebraMap K (AlgebraicClosure K))
  obtain ⟨β, hβ⟩ : ∃ β : o →+* AlgebraicClosure K, y ≫ x ≫ s = spMap β :=
    ⟨(Spec.preimage (y ≫ x ≫ s)).hom, (Spec.map_preimage _).symm⟩
  obtain ⟨hdet, I, hI, hA⟩ := hgeom _ y β hβ
  refine ⟨AlgebraicClosure K, inferInstance, inferInstance, inferInstance, y ≫ x, β,
    ⟨(default : PrimeSpectrum (AlgebraicClosure K)), ?_⟩, (Category.assoc _ _ _).trans hβ, fun σ => ?_,
    ObjPull.tateMove (ObjPull.pushEquiv hψ (Over.mk y)).symm (fun c z => ?_) (fun n z z' c hz => ?_) I, hI,
    fun i => Over.OverMorphism.ext (hA i)⟩
  · exact (Scheme.Hom.comp_apply y x _).trans ((congrArg x (Subsingleton.elim (α := PrimeSpectrum K) _ _)).trans hq)
  · rw [← LiePull.lieMult_pull _ _ _ t.A τ.G x ψ r τ.act hψ hc _ y σ,
      ← LiePull.lieMult_pull _ _ _ t.A τ.G x ψ r τ.act hψ hc _ y σ]
    exact hdet σ
  · obtain ⟨z, rfl⟩ := (ObjPull.pushEquiv hψ (Over.mk y)).surjective z
    rw [MulEquiv.symm_apply_eq, MulEquiv.symm_apply_apply]
    apply Over.OverMorphism.ext
    show (z.left ≫ _) ≫ _ = (z.left ≫ _) ≫ _
    rw [Category.assoc, ← hc, Category.assoc]
  · exact (weilIs_iff_of_isGrpPullback_comm _ _ t.A τ.G x ψ t.L τ.PP.L t.isLB τ.PP.isLB hψ hψL (Over.mk y) n _ _ z z' _
      (ObjPull.pushEquiv_symm_left hψ (Over.mk y) z).symm
      (ObjPull.pushEquiv_symm_left hψ (Over.mk y) z').symm).1 hz

/- English proof (translation)
Introduce `hL _ hcube E _ _ _ H D g J a bas w w' _ _ hw _ hcl k o _ b em ρ S _ _ s t hρ hem hd`. Use `t.ab.comm` as an intermediate fact. Take `⟨r, hra, hr⟩` from `GlobalTheory.T.oAct_spread_from_dense_fibres_abelianScheme (𝓞 E) J a S t.A t.act hcl t.ab t.hom (hd.mono fun p hp => by`. Take `⟨K, _, _, x, τ, ψ, hx, hψ, -, hact, -⟩` from `exists_fibre_map hL hcl hp`. Conclude with `⟨K, inferInstance, x, τ.G, inferInstance, ψ, τ.act, hx, hψ, hact⟩)`.

Establish `hadj` using `fun c => GlobalTheory.T.adjoint_endomorphisms_cubeLB_of_dense_fibres hL.globalFns S t.A t.L (r.act c) (r.act (H.bar c)) t.ab t.isLB t.ample (r.hom _) (r.hom _) (hd.mono fun p hp => by`. Take `⟨K, _, _, x, τ, ψ, hx, hψ, hψL, hact, -⟩` from `exists_fibre_map hL hcl hp`. Establish `hc` using `hr _ x τ.G ψ τ.act hψ hact`. Conclude with `⟨K, inferInstance, x, τ.G, inferInstance, inferInstance, ψ, τ.PP.L, _, _, hx, hψ, τ.PP.isLB, hψL, hc _, hc _, τ.adj c⟩)`. Establish `hprim` using `GlobalTheory.T.lbIso_cube_graph_of_dense_fibres hL.globalFns S t.A t.L (r.act H.w0) t.ab t.isLB t.ample t.rigid (r.hom _) (hd.mono fun p hp => by`.

Take `⟨K, _, _, x, τ, ψ, hx, hψ, hψL, hact, -⟩` from `exists_fibre_map hL hcl hp`. Establish `hc` using `hr _ x τ.G ψ τ.act hψ hact`. Conclude with `⟨K, inferInstance, x, τ.G, inferInstance, inferInstance, ψ, τ.PP.L, _, hx, hψ, τ.PP.isLB, hψL, hc _, τ.prim⟩)`. Take `⟨PP, cub, sym, iso, -, prim, adj⟩` from `PrimNorm.exists_primitive_normalisation hL.globalFns E H _ t.A r t.L t.ab t.isLB (hcube _ t.pol t.L t.isLB) hadj`. Establish `iso' : LBIso PP.L (t.L.pull (𝟙 t.A : t.A ⟶ t.A).left)`.

Use `LBIso.trans PP.isLB t.isLB (pull_isLB t.isLB _) (LBIso.trans PP.isLB (DVR.linComb_isLB _ t.isLB _ _) t.isLB iso hprim.symm) ?_` and prove the remaining obligations. Conclude with `(LBIso.chartPull (Geo.Tor.chartPullPull t.L (𝟙 _) (𝟙 _) rfl) (chartPullId t.L) (lbIso_refl t.isLB)).symm`. Use `⟨⟨t.A, isSemiAbelian_of_isAbelianScheme _ t.ab, r, PP, cub, sym, adj, prim⟩, Iso.refl _, inferInstanceAs (IsMonHom (𝟙 t.A)), iso', fun j => ?_, fun K _ _ _ x β hx => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Use `show r.act (a j) ≫ 𝟙 _ = 𝟙 _ ≫ t.act j`. Rewrite using `[hra, Category.comp_id, Category.id_comp]`.

Use `GlobalTheory.T.determinantCondition_spreads_of_dense_points E H D S t.A g r o s ρ t.dim (hem ?_) (hd.mono fun p hp => ?_) K x β hx` and prove the remaining obligations. Rewrite using `[map_pow, hρ, H.sqrt_neg_disc_sq, map_neg, map_natCast]`. Take `⟨K, _, _, _, x, β, h₁, h₂, h₃, -⟩` from `exists_geom hL hcl r hr hp`. Conclude with `⟨K, inferInstance, inferInstance, inferInstance, x, β, h₁, h₂, h₃⟩`. Establish `hk : 0 < k` using `Nat.pos_of_ne_zero fun h => by`.

Use `b.unit.map em` as an intermediate fact. Simplify using `[h] at this`. Establish `hcard : ∀ n, 0 < n → Nat.card {z : Over.mk x ⟶ t.A // z ^ n = 1} = n ^ Module.finrank ℤ D.La` using `fun n hn => by`. Rewrite using `[← bas.finrank_eq, Module.finrank_fin_fun]`. Conclude with `(hL.mulN S t.pol n hn).2.2.2.2 K x (Nat.cast_ne_zero.2 hn.ne')`.

Take `⟨I, hI, hA⟩` from `GlobalTheory.T.tateIsometry_of_finiteLevel_isometries E H D K (Over.mk x ⟶ t.A) (fun c z => z ≫ r.act c) (fun n z z' c => Out.WeilIs t.A t.L n z z' (unitOn c)) k (β b.ζ) _ (fun i => bas (Pi.single i 1)) (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ t.pt i) hk …`. Establish `e : unitOn (c ^ m) = unitOn c ^ m` using `map_pow _ _ _`. Establish `u : IsUnit ((n * m : ℕ) : K)` using `(Nat.cast_ne_zero.2 (Nat.mul_pos hn hm).ne').isUnit`. Establish `u'` using `u.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom`. Rewrite `u'` using `[map_natCast]`.

Rewrite using `[e]`. Conclude with `weilIs_lower t.pol hL.weil hm u' hz hz' h)`. Use the proof step `(fun m hm => by`. Establish `hn` using `Nat.mul_pos hk hm`. Take `⟨ζ, ev, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩` from `GlobalTheory.T.exists_level_isometry_of_dense_geometric_points hL E H D S t.pol r.act o s b.ζ _ (fun i => bas (Pi.single i 1)) t.pt (k * m) m hn (hd.mono fun p hp => by`.

Take `⟨K, _, _, _, x, β, h₁, h₂, -, I, h₃, h₄⟩` from `exists_geom hL hcl r hr hp`. Conclude with `⟨K, inferInstance, x, β, I.ζ (k * m), I.ev (k * m), Nat.cast_ne_zero.2 hn.ne', h₁, h₂, I.ζ_prim _ hn, I.add _, fun v => (I.onto _ hn _).2 ⟨v, rfl⟩, I.lin _, I.isom _ hn, by rw [← h₃, ← I.ζ_pow k m hk hm, Units.val_pow_eq_pow_val], fun i => (I.tower k m hk hm _).trans (h₄ i)⟩) K x …`. Take `⟨h₈, h₉⟩` from `GlobalTheory.T.torsionIsometry_primitiveRoot_bijective_mod_n E H D K (Over.mk x ⟶ t.A) (fun z z' c => Out.WeilIs t.A t.L (k * m : ℕ) z z' (unitOn c)) (k * m) ζ ev hn (hcard _ hn) (fun _ _ _ h => eq_one_of_weilIs_one t.pol hL.weil h) h₁ h₂ h₃ h₅`. Conclude with `⟨ζ, ev, h₁, h₂, h₄, h₈, h₉, h₅, h₆, h₇⟩)`. Conclude with `⟨{ I with isom := fun n hn z z' => weilIs_of_lbIso hL.globalFns t.ab PP.isLB t.isLB iso' (I.isom n hn z z') }, hI, fun i => (Category.comp_id _).trans (hA i)⟩`.
-/
theorem exists_isPEL_of_dense : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (w w' : J), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (ρ : o) (S : Scheme.{0}) [IsLocallyNoetherian S] [IsReduced S] (s : S ⟶ Sp o) (t : TObj g k J b s), em ρ = H.rt0 → Function.Injective em → Dense (fromSet em (PELClass (b := b) D a bas ρ em) t) → ∃ τ : SAB H S, IsPEL D a bas ρ t τ := by
  intro hL _ hcube E _ _ _ H D g J a bas w w' _ _ hw _ hcl k o _ b em ρ S _ _ s t hρ hem hd
  have := t.ab.comm
  obtain ⟨r, hra, hr⟩ := GlobalTheory.T.oAct_spread_from_dense_fibres_abelianScheme (𝓞 E) J a S t.A t.act hcl t.ab t.hom (hd.mono fun p hp => by
    obtain ⟨K, _, _, x, τ, ψ, hx, hψ, -, hact, -⟩ := exists_fibre_map hL hcl hp
    exact ⟨K, inferInstance, x, τ.G, inferInstance, ψ, τ.act, hx, hψ, hact⟩)
  have hadj := fun c => GlobalTheory.T.adjoint_endomorphisms_cubeLB_of_dense_fibres hL.globalFns S t.A t.L (r.act c) (r.act (H.bar c)) t.ab t.isLB t.ample (r.hom _)
    (r.hom _) (hd.mono fun p hp => by
      obtain ⟨K, _, _, x, τ, ψ, hx, hψ, hψL, hact, -⟩ := exists_fibre_map hL hcl hp
      have hc := hr _ x τ.G ψ τ.act hψ hact
      exact ⟨K, inferInstance, x, τ.G, inferInstance, inferInstance, ψ, τ.PP.L, _, _, hx, hψ, τ.PP.isLB, hψL, hc _, hc _,
        τ.adj c⟩)
  have hprim := GlobalTheory.T.lbIso_cube_graph_of_dense_fibres hL.globalFns S t.A t.L (r.act H.w0) t.ab t.isLB t.ample t.rigid (r.hom _)
    (hd.mono fun p hp => by
      obtain ⟨K, _, _, x, τ, ψ, hx, hψ, hψL, hact, -⟩ := exists_fibre_map hL hcl hp
      have hc := hr _ x τ.G ψ τ.act hψ hact
      exact ⟨K, inferInstance, x, τ.G, inferInstance, inferInstance, ψ, τ.PP.L, _, hx, hψ, τ.PP.isLB, hψL, hc _, τ.prim⟩)
  obtain ⟨PP, cub, sym, iso, -, prim, adj⟩ := PrimNorm.exists_primitive_normalisation hL.globalFns E H _ t.A r t.L t.ab
    t.isLB (hcube _ t.pol t.L t.isLB) hadj
  have iso' : LBIso PP.L (t.L.pull (𝟙 t.A : t.A ⟶ t.A).left) := by
    refine LBIso.trans PP.isLB t.isLB (pull_isLB t.isLB _)
      (LBIso.trans PP.isLB (DVR.linComb_isLB _ t.isLB _ _) t.isLB iso hprim.symm) ?_
    exact (LBIso.chartPull (Geo.Tor.chartPullPull t.L (𝟙 _) (𝟙 _) rfl) (chartPullId t.L) (lbIso_refl t.isLB)).symm
  refine ⟨⟨t.A, isSemiAbelian_of_isAbelianScheme _ t.ab, r, PP, cub, sym, adj, prim⟩, Iso.refl _,
    inferInstanceAs (IsMonHom (𝟙 t.A)), iso', fun j => ?_, fun K _ _ _ x β hx => ⟨?_, ?_⟩⟩
  · show r.act (a j) ≫ 𝟙 _ = 𝟙 _ ≫ t.act j
    rw [hra, Category.comp_id, Category.id_comp]
  · refine GlobalTheory.T.determinantCondition_spreads_of_dense_points E H D S t.A g r o s ρ t.dim (hem ?_) (hd.mono fun p hp => ?_) K x β hx
    · rw [map_pow, hρ, H.sqrt_neg_disc_sq, map_neg, map_natCast]
    · obtain ⟨K, _, _, _, x, β, h₁, h₂, h₃, -⟩ := exists_geom hL hcl r hr hp
      exact ⟨K, inferInstance, inferInstance, inferInstance, x, β, h₁, h₂, h₃⟩
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => by
    have := b.unit.map em
    simp [h] at this
  have hcard : ∀ n, 0 < n → Nat.card {z : Over.mk x ⟶ t.A // z ^ n = 1} = n ^ Module.finrank ℤ D.La := fun n hn => by
    rw [← bas.finrank_eq, Module.finrank_fin_fun]
    exact (hL.mulN S t.pol n hn).2.2.2.2 K x (Nat.cast_ne_zero.2 hn.ne')
  obtain ⟨I, hI, hA⟩ := GlobalTheory.T.tateIsometry_of_finiteLevel_isometries E H D K (Over.mk x ⟶ t.A) (fun c z => z ≫ r.act c)
    (fun n z z' c => Out.WeilIs t.A t.L n z z' (unitOn c)) k (β b.ζ) _ (fun i => bas (Pi.single i 1))
    (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ t.pt i) hk
    (fun n hn => Nat.finite_of_card_ne_zero (by rw [hcard n hn]; positivity))
    (fun n m z z' c hn hm hz hz' h => by
      have e : unitOn (c ^ m) = unitOn c ^ m := map_pow _ _ _
      have u : IsUnit ((n * m : ℕ) : K) := (Nat.cast_ne_zero.2 (Nat.mul_pos hn hm).ne').isUnit
      have u' := u.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      rw [map_natCast] at u'
      rw [e]
      exact weilIs_lower t.pol hL.weil hm u' hz hz' h)
    (fun m hm => by
      have hn := Nat.mul_pos hk hm
      obtain ⟨ζ, ev, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := GlobalTheory.T.exists_level_isometry_of_dense_geometric_points hL E H D S t.pol r.act o s b.ζ _
        (fun i => bas (Pi.single i 1)) t.pt (k * m) m hn (hd.mono fun p hp => by
          obtain ⟨K, _, _, _, x, β, h₁, h₂, -, I, h₃, h₄⟩ := exists_geom hL hcl r hr hp
          exact ⟨K, inferInstance, x, β, I.ζ (k * m), I.ev (k * m), Nat.cast_ne_zero.2 hn.ne', h₁, h₂, I.ζ_prim _ hn,
            I.add _, fun v => (I.onto _ hn _).2 ⟨v, rfl⟩, I.lin _, I.isom _ hn,
            by rw [← h₃, ← I.ζ_pow k m hk hm, Units.val_pow_eq_pow_val],
            fun i => (I.tower k m hk hm _).trans (h₄ i)⟩) K x β (Nat.cast_ne_zero.2 hn.ne') hx
      obtain ⟨h₈, h₉⟩ := GlobalTheory.T.torsionIsometry_primitiveRoot_bijective_mod_n E H D K (Over.mk x ⟶ t.A)
        (fun z z' c => Out.WeilIs t.A t.L (k * m : ℕ) z z' (unitOn c)) (k * m) ζ ev hn (hcard _ hn)
        (fun _ _ _ h => eq_one_of_weilIs_one t.pol hL.weil h) h₁ h₂ h₃ h₅
      exact ⟨ζ, ev, h₁, h₂, h₄, h₈, h₉, h₅, h₆, h₇⟩)
  exact ⟨{ I with isom := fun n hn z z' => weilIs_of_lbIso hL.globalFns t.ab PP.isLB t.isLB iso' (I.isom n hn z z') },
    hI, fun i => (Category.comp_id _).trans (hA i)⟩

end GlobalTheory.PELFamily
