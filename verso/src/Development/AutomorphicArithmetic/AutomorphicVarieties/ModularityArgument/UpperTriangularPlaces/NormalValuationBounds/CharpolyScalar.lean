import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.PtLawsOf
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CommonEigenvalue

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Polynomial Module UpperTheory.V.Z.Win

namespace UpperTheory.V.Keep

section linear

variable {k : Type} [Field k] [IsAlgClosed k]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.CommonEigenvectorOfCommutingSet.common_eig S hS`.
-/
private theorem common_eig {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (S : Set (End k V)) (hS : ∀ f ∈ S, ∀ f' ∈ S, f * f' = f' * f) :
    ∀ (d : ℕ) (W : Submodule k V), finrank k W = d → W ≠ ⊥ → (∀ f ∈ S, ∀ x ∈ W, f x ∈ W) →
      ∃ v ∈ W, v ≠ 0 ∧ ∀ f ∈ S, ∃ c : k, f v = c • v :=
  _root_.UpperTheory.Reformulated.B.CommonEigenvectorOfCommutingSet.common_eig S hS

/- English proof (translation)
Establish `hs : f = c • (1 : End k W)` using `LinearMap.ext fun x => by simp [hf]`. Rewrite using `[hs, ← LinearMap.charpoly_toMatrix _ (Module.finBasisOfFinrankEq k W hW), map_smul]`. Establish `: LinearMap.toMatrix (Module.finBasisOfFinrankEq k W hW) (Module.finBasisOfFinrankEq k W hW) (1 : End k W) = 1` using `LinearMap.toMatrix_one _`. Rewrite using `[this, Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal]`. Simplify using the standard rewrite rules.
-/
private theorem charpoly_scalar {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W] (hW : finrank k W = 1)
    (f : End k W) (c : k) (hf : ∀ x, f x = c • x) : f.charpoly = X - C c := by
  have hs : f = c • (1 : End k W) := LinearMap.ext fun x => by simp [hf]
  rw [hs, ← LinearMap.charpoly_toMatrix _ (Module.finBasisOfFinrankEq k W hW), map_smul]
  have : LinearMap.toMatrix (Module.finBasisOfFinrankEq k W hW) (Module.finBasisOfFinrankEq k W hW) (1 : End k W) = 1 :=
    LinearMap.toMatrix_one _
  rw [this, Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal]
  simp

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `V _ _ _ ρ _ hd`. Use `⟨fun i => i.elim0, fun g => ?_⟩` and prove the remaining obligations.

Simplify using `using eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic (ρ g)) (by rw [LinearMap.charpoly_natDegree, hd])`. Consider the case `succ d ih`. Introduce `V _ _ _ ρ hc hd`. Use `haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by omega)`. Take `⟨v, -, hv0, hv⟩` from `common_eig (Set.range ρ) (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact hc a b) _ ⊤ rfl top_ne_bot (fun _ _ _ _ => trivial)`.

Use `choose c hcv using fun g => hv (ρ g) ⟨g, rfl⟩`. Establish `inj : ∀ a b : k, a • v = b • v → a = b` using `fun a b h => smul_left_injective k hv0 h`. Set `c0 : Γ →* k` to `{ toFun := c map_one' := inj _ _ (by rw [← hcv, map_one]; simp) map_mul' := fun a b => inj _ _ (by`. Rewrite using `[← hcv, map_mul, Module.End.mul_apply, hcv b, map_smul, hcv a, smul_smul, mul_comm]) }`. Set `W : Submodule k V` to `Submodule.span k {v}`.

Establish `hvW : v ∈ W` using `Submodule.mem_span_singleton_self v`. Establish `hW : ∀ g, ∀ x ∈ W, ρ g x ∈ W`. Introduce `g x hx`. Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.1 hx`. Rewrite using `[map_smul, hcv]`.

Conclude with `W.smul_mem _ (W.smul_mem _ hvW)`. Set `ρ' : Γ →* End k (V ⧸ W)` to `{ toFun := fun g => W.mapQ W (ρ g) (fun x hx => hW g x hx) map_one' := by`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `Submodule.mkQ_surjective W x`. Simplify using the standard rewrite rules.

Use the proof step `map_mul' := fun a b => by`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `Submodule.mkQ_surjective W x`. Simplify using `[Module.End.mul_apply] }`. Establish `hW1 : finrank k W = 1` using `finrank_span_singleton hv0`.

Establish `hq : finrank k (V ⧸ W) = d`. Use `Submodule.finrank_quotient_add_finrank W` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨χ, hχ⟩` from `ih (V ⧸ W) ρ' (fun a b => by`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations.

Take `⟨y, rfl⟩` from `Submodule.mkQ_surjective W x`. Establish `h1 : ρ a (ρ b y) = ρ b (ρ a y)` using `LinearMap.congr_fun (hc a b) y`. Simplify using `[ρ', Module.End.mul_apply, h1]) hq`. Use `⟨Fin.cons c0.toHomUnits χ, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.prod_univ_succ, GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ W (ρ g) (hW g)]`.

Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Use `congr 1`. Use `charpoly_scalar hW1 _ _ fun x => Subtype.ext ?_` and prove the remaining obligations. Take `⟨x, hx⟩` from `x`. Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.1 hx`.

Use `show ρ g (a • v) = c g • a • v`. Rewrite using `[map_smul, hcv, smul_comm]`. Conclude with `hχ g`.
-/
private theorem chars_of_comm {Γ : Type} [Group Γ] :
    ∀ (d : ℕ) (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Γ →* End k V),
      (∀ a b, ρ a * ρ b = ρ b * ρ a) → finrank k V = d →
      ∃ χ : Fin d → Γ →* kˣ, ∀ g, (ρ g).charpoly = ∏ i, (X - C (χ i g : k)) := by
  intro d
  induction d with
  | zero =>
    intro V _ _ _ ρ _ hd
    refine ⟨fun i => i.elim0, fun g => ?_⟩
    simpa using eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic (ρ g))
      (by rw [LinearMap.charpoly_natDegree, hd])
  | succ d ih =>
    intro V _ _ _ ρ hc hd
    haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by omega)
    obtain ⟨v, -, hv0, hv⟩ := common_eig (Set.range ρ)
      (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact hc a b) _ ⊤ rfl top_ne_bot (fun _ _ _ _ => trivial)
    choose c hcv using fun g => hv (ρ g) ⟨g, rfl⟩
    have inj : ∀ a b : k, a • v = b • v → a = b := fun a b h => smul_left_injective k hv0 h
    let c0 : Γ →* k :=
      { toFun := c
        map_one' := inj _ _ (by rw [← hcv, map_one]; simp)
        map_mul' := fun a b => inj _ _ (by
          rw [← hcv, map_mul, Module.End.mul_apply, hcv b, map_smul, hcv a, smul_smul, mul_comm]) }
    let W : Submodule k V := Submodule.span k {v}
    have hvW : v ∈ W := Submodule.mem_span_singleton_self v
    have hW : ∀ g, ∀ x ∈ W, ρ g x ∈ W := by
      intro g x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
      rw [map_smul, hcv]
      exact W.smul_mem _ (W.smul_mem _ hvW)
    let ρ' : Γ →* End k (V ⧸ W) :=
      { toFun := fun g => W.mapQ W (ρ g) (fun x hx => hW g x hx)
        map_one' := by
          refine LinearMap.ext fun x => ?_
          obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective W x
          simp
        map_mul' := fun a b => by
          refine LinearMap.ext fun x => ?_
          obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective W x
          simp [Module.End.mul_apply] }
    have hW1 : finrank k W = 1 := finrank_span_singleton hv0
    have hq : finrank k (V ⧸ W) = d := by
      have := Submodule.finrank_quotient_add_finrank W
      omega
    obtain ⟨χ, hχ⟩ := ih (V ⧸ W) ρ' (fun a b => by
      refine LinearMap.ext fun x => ?_
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective W x
      have h1 : ρ a (ρ b y) = ρ b (ρ a y) := LinearMap.congr_fun (hc a b) y
      simp [ρ', Module.End.mul_apply, h1]) hq
    refine ⟨Fin.cons c0.toHomUnits χ, fun g => ?_⟩
    rw [Fin.prod_univ_succ, GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ W (ρ g) (hW g)]
    simp only [Fin.cons_zero, Fin.cons_succ]
    congr 1
    · refine charpoly_scalar hW1 _ _ fun x => Subtype.ext ?_
      obtain ⟨x, hx⟩ := x
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
      show ρ g (a • v) = c g • a • v
      rw [map_smul, hcv, smul_comm]
    · exact hχ g

/- English proof (translation)
Set `φ : Γ →* End k (Fin n → k)` to `{ toFun := fun g => Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) k) map_one' := by simp; rfl map_mul' := fun a b => by simp [Matrix.toLin'_mul]; rfl }`. Take `⟨χ, h⟩` from `chars_of_comm n (Fin n → k) φ (fun a b => by show Matrix.toLin' _ * Matrix.toLin' _ = Matrix.toLin' _ * Matrix.toLin' _`. Establish `h1` using `congrArg (fun x : Matrix.GeneralLinearGroup (Fin n) k => (x : Matrix (Fin n) (Fin n) k)) (hc a b)`. Simplify using `only [Units.val_mul] at h1`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations.

Simplify using `only [Module.End.mul_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, h1]) (by simp)`. Use `⟨χ, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[← h g]`. Use `LinearMap.charpoly_toMatrix (φ g) (Pi.basisFun k (Fin n))` as an intermediate fact. Rewrite using `[← this, LinearMap.toMatrix_eq_toMatrix']`.

Use `show _ = (LinearMap.toMatrix' (Matrix.toLin' _)).charpoly`. Rewrite using `[LinearMap.toMatrix'_toLin']`.
-/
private theorem chars_of_gl {Γ : Type} [Group Γ] {n : ℕ} (ρ : Γ →* Matrix.GeneralLinearGroup (Fin n) k)
    (hc : ∀ a b, ρ a * ρ b = ρ b * ρ a) :
    ∃ χ : Fin n → Γ →* kˣ, ∀ g, (ρ g : Matrix (Fin n) (Fin n) k).charpoly = ∏ i, (X - C (χ i g : k)) := by
  let φ : Γ →* End k (Fin n → k) :=
    { toFun := fun g => Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) k)
      map_one' := by simp; rfl
      map_mul' := fun a b => by simp [Matrix.toLin'_mul]; rfl }
  obtain ⟨χ, h⟩ := chars_of_comm n (Fin n → k) φ (fun a b => by
    show Matrix.toLin' _ * Matrix.toLin' _ = Matrix.toLin' _ * Matrix.toLin' _
    have h1 := congrArg (fun x : Matrix.GeneralLinearGroup (Fin n) k => (x : Matrix (Fin n) (Fin n) k)) (hc a b)
    simp only [Units.val_mul] at h1
    refine LinearMap.ext fun x => ?_
    simp only [Module.End.mul_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, h1]) (by simp)
  refine ⟨χ, fun g => ?_⟩
  rw [← h g]
  have := LinearMap.charpoly_toMatrix (φ g) (Pi.basisFun k (Fin n))
  rw [← this, LinearMap.toMatrix_eq_toMatrix']
  show _ = (LinearMap.toMatrix' (Matrix.toLin' _)).charpoly
  rw [LinearMap.toMatrix'_toLin']

end linear

section extend

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]

/- English proof (translation)
Use `haveI : NeZero (Monoid.exponent Q) := ⟨Monoid.exponent_ne_zero_of_finite⟩`. Establish `hk : f.rangeRestrict.ker ≤ χ.ker` using `by rwa [MonoidHom.ker_rangeRestrict]`. Set `χ' : f.range →* kˣ` to `f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective ⟨χ, hk⟩`. Take `⟨ψ, hψ⟩` from `MonoidHom.restrict_surjective k f.range χ'`. Use `⟨ψ, MonoidHom.ext fun g => ?_⟩` and prove the remaining obligations.

Establish `h1 : χ' (f.rangeRestrict g) = χ g` using `MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨χ, hk⟩ g`. Rewrite using `[← h1, ← hψ]`. Both sides reduce to the same expression.
-/
private theorem extend_char {Γ Q : Type} [Group Γ] [CommGroup Q] [Finite Q] (f : Γ →* Q) (χ : Γ →* kˣ)
    (h : f.ker ≤ χ.ker) : ∃ ψ : Q →* kˣ, ψ.comp f = χ := by
  haveI : NeZero (Monoid.exponent Q) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have hk : f.rangeRestrict.ker ≤ χ.ker := by rwa [MonoidHom.ker_rangeRestrict]
  let χ' : f.range →* kˣ := f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective ⟨χ, hk⟩
  obtain ⟨ψ, hψ⟩ := MonoidHom.restrict_surjective k f.range χ'
  refine ⟨ψ, MonoidHom.ext fun g => ?_⟩
  have h1 : χ' (f.rangeRestrict g) = χ g :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨χ, hk⟩ g
  rw [← h1, ← hψ]
  rfl

/- English proof (translation)
Establish `hcm : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ H` using `fun a b => hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))`. Use `haveI hN : H.Normal := ⟨fun h hh g => by`. Establish `h1` using `H.mul_mem (hcm g h) hh`. Simplify `h1⟩` using `[mul_assoc]`. Use `haveI : Finite (Γ ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH`.

Use `letI : CommGroup (Γ ⧸ H) := { (QuotientGroup.Quotient.group H) with mul_comm := fun x y => by`. Proceed by induction on `x using QuotientGroup.induction_on with | _ a =>`. Proceed by induction on `y using QuotientGroup.induction_on with | _ b =>`. Rewrite using `[← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]`. Establish `h1` using `hcm b⁻¹ a⁻¹`.

Simplify `h1 }` using `[mul_assoc]`. Set `π : Γ →* Γ ⧸ H` to `QuotientGroup.mk' H`. Establish `hπ : ∀ g, π g = 1 ↔ g ∈ H` using `fun g => QuotientGroup.eq_one_iff g`. Establish `hcomm : ∀ a b : ↥I, (r.comp I.subtype) a * (r.comp I.subtype) b = (r.comp I.subtype) b * (r.comp I.subtype) a`. Introduce `a b`.

Establish `h1 : r ((a : Γ) * b * (a : Γ)⁻¹ * (b : Γ)⁻¹) = 1` using `ht _ (I.mul_mem (I.mul_mem (I.mul_mem a.2 b.2) (I.inv_mem a.2)) (I.inv_mem b.2)) (hcm a b)`. Simplify using `only [map_mul, map_inv] at h1`. Simplify using `only [MonoidHom.comp_apply, Subgroup.subtype_apply]`. Establish `h2` using `mul_inv_eq_one.1 h1`. Conclude with `mul_inv_eq_iff_eq_mul.1 h2`.

Take `⟨χ, hχ⟩` from `chars_of_gl (r.comp I.subtype) hcomm`. Establish `hker : ∀ i, (π.comp I.subtype).ker ≤ (χ i).ker`. Introduce `i g hg`. Establish `hgH : (g : Γ) ∈ H` using `(hπ _).1 hg`. Establish `h1` using `hχ g`.

Establish `h2 : (r.comp I.subtype) g = 1` using `ht _ g.2 hgH`. Rewrite `h1` using `[h2, Units.val_one, Matrix.charpoly_one]`. Establish `h3` using `congrArg (Polynomial.eval ((χ i g : kˣ) : k)) h1`. Rewrite `h3` using `[Polynomial.eval_prod, Finset.prod_eq_zero (Finset.mem_univ i) (by simp)]`. Simplify using `only [eval_pow, eval_sub, eval_X, eval_one] at h3`.

Establish `h4 : ((χ i g : kˣ) : k) - 1 = 0` using `(pow_eq_zero_iff (by have := i.pos; simp; omega)).1 h3`. Conclude with `Units.ext (sub_eq_zero.1 h4)`. Use `choose ψ hψ using fun i => extend_char (π.comp I.subtype) (χ i) (hker i)`. Use `⟨fun i => ((ψ i).comp π).comp D.subtype, fun i => ?_, fun g hg => ?_⟩` and prove the remaining obligations. Establish `hcont : Continuous ((ψ i).comp π)`.

Use `IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun x => ⟨(fun y => x⁻¹ * y) ⁻¹' (H : Set Γ), hH.preimage (continuous_const.mul continuous_id), ?_, fun y hy => ?_⟩)` and prove the remaining obligations. Simplify using `[H.one_mem]`. Establish `h1 : π (x⁻¹ * y) = 1` using `(hπ _).2 hy`. Establish `h2 : π y = π x`. Rewrite `h1` using `[map_mul, map_inv]`.

Conclude with `(inv_mul_eq_one.1 h1).symm`. Simplify using `[h2]`. Conclude with `hcont.comp continuous_subtype_val`. Establish `h1` using `hχ ⟨g, hg⟩`. Simplify using `only [MonoidHom.comp_apply, Subgroup.subtype_apply] at h1 ⊢`.

Rewrite using `[h1]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← hψ i]`. Both sides reduce to the same expression.
-/
private theorem descend [TopologicalSpace k] {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] {n : ℕ} (r : Γ →* Matrix.GeneralLinearGroup (Fin n) k) (H : Subgroup Γ) (hH : IsOpen (H : Set Γ))
    (hc : commutator Γ ≤ H) (I D : Subgroup Γ) (ht : ∀ g ∈ I, g ∈ H → r g = 1) :
    ∃ κ : Fin n → ↥D →* kˣ, (∀ i, Continuous (κ i)) ∧ ∀ g : ↥D, (g : Γ) ∈ I →
      (r g : Matrix (Fin n) (Fin n) k).charpoly = ∏ i, (X - C (κ i g : k)) := by
  have hcm : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ H := fun a b =>
    hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
  haveI hN : H.Normal := ⟨fun h hh g => by
    have h1 := H.mul_mem (hcm g h) hh
    simpa [mul_assoc] using h1⟩
  haveI : Finite (Γ ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  letI : CommGroup (Γ ⧸ H) :=
    { (QuotientGroup.Quotient.group H) with
      mul_comm := fun x y => by
        induction x using QuotientGroup.induction_on with | _ a =>
        induction y using QuotientGroup.induction_on with | _ b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have h1 := hcm b⁻¹ a⁻¹
        simpa [mul_assoc] using h1 }
  let π : Γ →* Γ ⧸ H := QuotientGroup.mk' H
  have hπ : ∀ g, π g = 1 ↔ g ∈ H := fun g => QuotientGroup.eq_one_iff g
  have hcomm : ∀ a b : ↥I, (r.comp I.subtype) a * (r.comp I.subtype) b = (r.comp I.subtype) b * (r.comp I.subtype) a := by
    intro a b
    have h1 : r ((a : Γ) * b * (a : Γ)⁻¹ * (b : Γ)⁻¹) = 1 :=
      ht _ (I.mul_mem (I.mul_mem (I.mul_mem a.2 b.2) (I.inv_mem a.2)) (I.inv_mem b.2)) (hcm a b)
    simp only [map_mul, map_inv] at h1
    simp only [MonoidHom.comp_apply, Subgroup.subtype_apply]
    have h2 := mul_inv_eq_one.1 h1
    exact mul_inv_eq_iff_eq_mul.1 h2
  obtain ⟨χ, hχ⟩ := chars_of_gl (r.comp I.subtype) hcomm
  have hker : ∀ i, (π.comp I.subtype).ker ≤ (χ i).ker := by
    intro i g hg
    have hgH : (g : Γ) ∈ H := (hπ _).1 hg
    have h1 := hχ g
    have h2 : (r.comp I.subtype) g = 1 := ht _ g.2 hgH
    rw [h2, Units.val_one, Matrix.charpoly_one] at h1
    have h3 := congrArg (Polynomial.eval ((χ i g : kˣ) : k)) h1
    rw [Polynomial.eval_prod, Finset.prod_eq_zero (Finset.mem_univ i) (by simp)] at h3
    simp only [eval_pow, eval_sub, eval_X, eval_one] at h3
    have h4 : ((χ i g : kˣ) : k) - 1 = 0 := (pow_eq_zero_iff (by have := i.pos; simp; omega)).1 h3
    exact Units.ext (sub_eq_zero.1 h4)
  choose ψ hψ using fun i => extend_char (π.comp I.subtype) (χ i) (hker i)
  refine ⟨fun i => ((ψ i).comp π).comp D.subtype, fun i => ?_, fun g hg => ?_⟩
  · have hcont : Continuous ((ψ i).comp π) := by
      refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun x =>
        ⟨(fun y => x⁻¹ * y) ⁻¹' (H : Set Γ), hH.preimage (continuous_const.mul continuous_id), ?_, fun y hy => ?_⟩)
      · simp [H.one_mem]
      · have h1 : π (x⁻¹ * y) = 1 := (hπ _).2 hy
        have h2 : π y = π x := by
          rw [map_mul, map_inv] at h1
          exact (inv_mul_eq_one.1 h1).symm
        simp [h2]
    exact hcont.comp continuous_subtype_val
  · have h1 := hχ ⟨g, hg⟩
    simp only [MonoidHom.comp_apply, Subgroup.subtype_apply] at h1 ⊢
    rw [h1]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← hψ i]
    rfl

end extend

/- English proof (translation)
Introduce `Ω _ _ _ l _ n r H hH hc ht v hv A hA`. Establish `hl : ¬ A.valuation (l : Ω) < 1`. Introduce `h`. Use `hv ((hA ((l : ℕ) : 𝓞 ℚ)).1 ?_)` and prove the remaining obligations. Simplify using `using h`.

Conclude with `descend r H hH hc (Ine (F := ℚ) A) (Dec (F := ℚ) A) (ht A hl)`.
-/
theorem ineOf : IneOf := by
  intro Ω _ _ _ l _ n r H hH hc ht v hv A hA
  have hl : ¬ A.valuation (l : Ω) < 1 := by
    intro h
    refine hv ((hA ((l : ℕ) : 𝓞 ℚ)).1 ?_)
    simpa using h
  exact descend r H hH hc (Ine (F := ℚ) A) (Dec (F := ℚ) A) (ht A hl)

end UpperTheory.V.Keep
