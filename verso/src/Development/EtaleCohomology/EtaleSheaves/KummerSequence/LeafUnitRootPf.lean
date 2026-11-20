import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumSecSurjPf

open Polynomial
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.H2CurveOrder.LeafKumSeqPf LateralTheory.E.H2CurveOrder.KummerH0Surjection
namespace LateralTheory.E.H2CurveOrder.LeafUnitRootPf
variable {R : Type} [CommRing R]

noncomputable def kf (q : ℕ) (b : Rˣ) : R[X] := X ^ q - C (b : R)

/- English proof (translation)
The claim follows from `monic_X_pow_sub_C _ (NeZero.ne q)`.
-/
theorem kf_monic (q : ℕ) [NeZero q] (b : Rˣ) : (kf q b).Monic :=
  monic_X_pow_sub_C _ (NeZero.ne q)

noncomputable def kpair (q : ℕ) [NeZero q] (hq : IsUnit (q : R)) (b : Rˣ) : StandardEtalePair R where
  f := kf q b
  monic_f := kf_monic q b
  g := 1
  cond := by
    refine ⟨C (↑hq.unit⁻¹ : R) * C (↑b⁻¹ : R) * X, -C (↑b⁻¹ : R), 0, ?_⟩
    have h1 : C (q : R) * C (↑hq.unit⁻¹ : R) = 1 := by
      rw [← C_mul, ← map_one C]; congr 1; simpa using hq.mul_val_inv
    have h2 : C (b : R) * C (↑b⁻¹ : R) = 1 := by
      rw [← C_mul, ← map_one C]; simp
    have h3 : (X : R[X]) ^ (q - 1) * X = X ^ q := pow_sub_one_mul (NeZero.ne q) _
    simp only [kf, derivative_sub, derivative_X_pow, derivative_C, sub_zero, pow_zero]
    linear_combination (C (q : R) * C (↑hq.unit⁻¹ : R) * C (↑b⁻¹ : R)) * h3 +
      (C (↑b⁻¹ : R) * X ^ q) * h1 + h2

/- English proof (translation)
Assemble the required witnesses or components as `⟨by simp [kpair], by simp [kpair]⟩`.
-/
theorem kpair_hasMap (q : ℕ) [NeZero q] (hq : IsUnit (q : R)) (b : Rˣ) :
    (kpair q hq b).HasMap (AdjoinRoot.root (kf q b)) :=
  ⟨by simp [kpair], by simp [kpair]⟩

noncomputable def kpres (q : ℕ) [NeZero q] (hq : IsUnit (q : R)) (b : Rˣ) :
    StandardEtalePresentation R (AdjoinRoot (kf q b)) where
  P := kpair q hq b
  x := AdjoinRoot.root (kf q b)
  hasMap := kpair_hasMap q hq b
  lift_bijective := by
    let Q := kpair q hq b
    let φ := Q.lift _ (kpair_hasMap q hq b)
    have hX : Polynomial.aeval Q.X (kf q b) = 0 := Q.hasMap_X.1
    let ψ : AdjoinRoot (kf q b) →ₐ[R] Q.Ring := AdjoinRoot.liftAlgHom (kf q b) (Algebra.ofId R Q.Ring) Q.X
      (by simpa [Polynomial.aeval_def] using hX)
    have e1 : ψ.comp φ = AlgHom.id R _ := Q.hom_ext (by simp [φ, ψ])
    have e2 : φ.comp ψ = AlgHom.id R _ := AdjoinRoot.algHom_ext (by simp [φ, ψ])
    exact ⟨Function.LeftInverse.injective (g := ψ) (fun x => congrArg (· x) e1),
      Function.RightInverse.surjective (g := ψ) (fun x => congrArg (· x) e2)⟩

instance (q : ℕ) [NeZero q] [Fact (IsUnit (q : R))] (b : Rˣ) : Algebra.IsStandardEtale R (AdjoinRoot (kf q b)) :=
  ⟨⟨kpres q Fact.out b⟩⟩

/- English proof (translation)
Establish `: Fact (IsUnit (q : R))` using `⟨hq⟩`. Use `infer_instance`.
-/
theorem kf_etale (q : ℕ) [NeZero q] (hq : IsUnit (q : R)) (b : Rˣ) : Algebra.Etale R (AdjoinRoot (kf q b)) := by
  have : Fact (IsUnit (q : R)) := ⟨hq⟩; infer_instance

/- English proof (translation)
Break down `subsingleton_or_nontrivial R with hR | hR` into its components or cases. Introduce `p`. Conclude with `(p.isPrime.ne_top (Subsingleton.elim _ _)).elim`. Set `pb` to `AdjoinRoot.powerBasis' (kf_monic q b)`. Establish `: Module.Free R (AdjoinRoot (kf q b))` using `Module.Free.of_basis pb.basis`.

Establish `hd : 0 < pb.dim`. Establish `: (kf q b).natDegree = q` using `natDegree_X_pow_sub_C`. Express the relevant statement in the definitionally equal form `0 < (kf q b).natDegree`. Rewrite using `[this]`. Conclude with `Nat.pos_of_ne_zero (NeZero.ne q)`.

Establish `: Nontrivial (AdjoinRoot (kf q b))` using `nontrivial_of_ne _ _ (pb.basis.ne_zero ⟨0, hd⟩)`. Conclude with `PrimeSpectrum.comap_surjective_of_faithfullyFlat`.
-/
theorem kf_comap_surj (q : ℕ) [NeZero q] (b : Rˣ) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap R (AdjoinRoot (kf q b)))) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · intro p; exact (p.isPrime.ne_top (Subsingleton.elim _ _)).elim
  · let pb := AdjoinRoot.powerBasis' (kf_monic q b)
    have : Module.Free R (AdjoinRoot (kf q b)) := Module.Free.of_basis pb.basis
    have hd : 0 < pb.dim := by
      have : (kf q b).natDegree = q := natDegree_X_pow_sub_C
      change 0 < (kf q b).natDegree
      rw [this]; exact Nat.pos_of_ne_zero (NeZero.ne q)
    have : Nontrivial (AdjoinRoot (kf q b)) := nontrivial_of_ne _ _ (pb.basis.ne_zero ⟨0, hd⟩)
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat

section geo
variable (q : ℕ) [NeZero q] (V : Scheme.{0}) (b : (Γ(V, ⊤))ˣ)

noncomputable abbrev kA : CommRingCat.{0} := CommRingCat.of (AdjoinRoot (kf q b))
noncomputable abbrev kφ : Γ(V, ⊤) ⟶ kA q V b := CommRingCat.ofHom (algebraMap _ _)
noncomputable abbrev kW : Scheme.{0} := pullback V.toSpecΓ (Spec.map (kφ q V b))
noncomputable abbrev kπ : kW q V b ⟶ V := pullback.fst _ _

/- English proof (translation)
Use `kf_etale q hq b` as an intermediate fact. Establish `h1 : Etale (Spec.map (kφ q V b))`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Etale)]`. Conclude with `RingHom.etale_algebraMap.2 this`. Establish `h2 : Surjective (Spec.map (kφ q V b))`.

Use `((flat_and_surjective_SpecMap_iff (kφ q V b)).2 ?_).2` and prove the remaining obligations. Use `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.2 ⟨?_, kf_comap_surj q b⟩` and prove the remaining obligations. Conclude with `RingHom.flat_algebraMap_iff.2 inferInstance`. Conclude with `⟨inferInstance, inferInstance⟩`.
-/
theorem kπ_etale_surj (hq : IsUnit (q : Γ(V, ⊤))) : Etale (kπ q V b) ∧ Surjective (kπ q V b) := by
  have := kf_etale q hq b
  have h1 : Etale (Spec.map (kφ q V b)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.2 this
  have h2 : Surjective (Spec.map (kφ q V b)) := by
    refine ((flat_and_surjective_SpecMap_iff (kφ q V b)).2 ?_).2
    refine RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.2 ⟨?_, kf_comap_surj q b⟩
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  exact ⟨inferInstance, inferInstance⟩

noncomputable abbrev kψ : kA q V b ⟶ Γ(kW q V b, ⊤) :=
  (Scheme.ΓSpecIso (kA q V b)).inv ≫ (pullback.snd V.toSpecΓ (Spec.map (kφ q V b))).appTop

/- English proof (translation)
Establish `hnat : kφ q V b ≫ (Scheme.ΓSpecIso (kA q V b)).inv = (Scheme.ΓSpecIso Γ(V, ⊤)).inv ≫ (Spec.map (kφ q V b)).appTop`. Rewrite using `[Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]`. Conclude with `(Scheme.ΓSpecIso_naturality _).symm`. Establish `hc : V.toSpecΓ.appTop ≫ (kπ q V b).appTop = (Spec.map (kφ q V b)).appTop ≫ (pullback.snd V.toSpecΓ (Spec.map (kφ q V b))).appTop`. Rewrite using `[← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, pullback.condition]`.

Rewrite using `[← Category.assoc, hnat, Category.assoc, ← hc, Scheme.toSpecΓ_appTop, Iso.inv_hom_id_assoc]`.
-/
theorem kφ_kψ : kφ q V b ≫ kψ q V b = (kπ q V b).appTop := by
  have hnat : kφ q V b ≫ (Scheme.ΓSpecIso (kA q V b)).inv =
      (Scheme.ΓSpecIso Γ(V, ⊤)).inv ≫ (Spec.map (kφ q V b)).appTop := by
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
    exact (Scheme.ΓSpecIso_naturality _).symm
  have hc : V.toSpecΓ.appTop ≫ (kπ q V b).appTop =
      (Spec.map (kφ q V b)).appTop ≫ (pullback.snd V.toSpecΓ (Spec.map (kφ q V b))).appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, pullback.condition]
  rw [← Category.assoc, hnat, Category.assoc, ← hc, Scheme.toSpecΓ_appTop, Iso.inv_hom_id_assoc]

/- English proof (translation)
Establish `h` using `(toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).naturality f.op`. Conclude with `(ConcreteCategory.congr_hom h ⟨x⟩).symm`.
-/
theorem unitsToSec_nat {U W : Scheme.{0}} (f : W ⟶ U) (x : Additive (Γ(U, ⊤))ˣ) :
    Gm.obj.map f.op (unitsToSec U x) = unitsToSec W (Additive.ofMul (Units.map f.appTop.hom x.toMul)) := by
  have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).naturality f.op
  exact (ConcreteCategory.congr_hom h ⟨x⟩).symm
end geo

/- English proof (translation)
Introduce `q _ V hq b`. Take `⟨he, hs⟩` from `kπ_etale_surj q V b hq`. Use `Scheme.etaleTopology.superset_covering ?_ (Precoverage.generate_mem_toGrothendieck ((Scheme.singleton_mem_precoverage_iff (P := @Etale) (kπ q V b)).2 ⟨hs.surj, he⟩))` and prove the remaining obligations. Rewrite using `[Sieve.generate_le_iff]`. Introduce and unpack `_ _ ⟨⟩`.

Establish `hroot : (AdjoinRoot.root (kf q b)) ^ q = algebraMap _ (AdjoinRoot (kf q b)) (b : Γ(V, ⊤))`. Establish `h2 : AdjoinRoot.mk (kf q b) (X ^ q - C (b : Γ(V, ⊤))) = 0` using `AdjoinRoot.mk_self`. Rewrite `h2` using `[map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C]`. Conclude with `sub_eq_zero.1 h2`. Establish `hu : IsUnit (AdjoinRoot.root (kf q b))` using `(isUnit_pow_iff (NeZero.ne q)).1 (hroot ▸ b.isUnit.map _)`.

Use `⟨unitsToSec _ (Additive.ofMul (Units.map (kψ q V b).hom hu.unit)), ?_⟩` and prove the remaining obligations. Establish `e` using `pow_unitsToSec q (kW q V b) (Additive.ofMul (Units.map (kψ q V b).hom hu.unit))`. Use `e.trans ?_` and prove the remaining obligations. Rewrite using `[unitsToSec_nat]`. Use `congr 1`.

Apply `Additive.toMul.injective` to reduce the goal to its premises. Use `ext`. Simplify using `only [toMul_nsmul, toMul_ofMul, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe, IsUnit.unit_spec]`. Rewrite using `[← map_pow, hroot, ← kφ_kψ]`. Both sides reduce to the same expression.
-/
theorem LeafUnitRoot_of : LateralTheory.E.H2CurveOrder.LeafKumSecSurjPf.LeafUnitRoot := by
  intro q _ V hq b
  obtain ⟨he, hs⟩ := kπ_etale_surj q V b hq
  refine Scheme.etaleTopology.superset_covering ?_ (Precoverage.generate_mem_toGrothendieck
    ((Scheme.singleton_mem_precoverage_iff (P := @Etale) (kπ q V b)).2 ⟨hs.surj, he⟩))
  rw [Sieve.generate_le_iff]
  rintro _ _ ⟨⟩
  have hroot : (AdjoinRoot.root (kf q b)) ^ q = algebraMap _ (AdjoinRoot (kf q b)) (b : Γ(V, ⊤)) := by
    have h2 : AdjoinRoot.mk (kf q b) (X ^ q - C (b : Γ(V, ⊤))) = 0 := AdjoinRoot.mk_self
    rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h2
    exact sub_eq_zero.1 h2
  have hu : IsUnit (AdjoinRoot.root (kf q b)) :=
    (isUnit_pow_iff (NeZero.ne q)).1 (hroot ▸ b.isUnit.map _)
  refine ⟨unitsToSec _ (Additive.ofMul (Units.map (kψ q V b).hom hu.unit)), ?_⟩
  have e := pow_unitsToSec q (kW q V b) (Additive.ofMul (Units.map (kψ q V b).hom hu.unit))
  refine e.trans ?_
  rw [unitsToSec_nat]
  congr 1
  apply Additive.toMul.injective
  ext
  simp only [toMul_nsmul, toMul_ofMul, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe,
    IsUnit.unit_spec]
  rw [← map_pow, hroot, ← kφ_kψ]
  rfl

end LateralTheory.E.H2CurveOrder.LeafUnitRootPf
