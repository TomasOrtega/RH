import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrimeStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FamDim

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

/- English proof (translation)
Set `B` to `(Module.finBasis ℤ X).equivFun`. Establish `hk' : (0 : ℤ) < k` using `by exact_mod_cast hk`. Use `⟨fun q => B.symm (fun i => ((q i : ℕ) : ℤ)), fun q q' mu h => ?_, fun β => ?_, fun a b h => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Establish `e` using `congrFun (congrArg B h) i`.

Simplify using `only [map_add, map_nsmul, LinearEquiv.apply_symm_apply, Pi.add_apply, Pi.smul_apply] at e`. Rewrite `e` using `[nsmul_eq_mul]`. Establish `e2` using `congrArg (· % (k : ℤ)) e`. Simplify using `only [Int.add_mul_emod_self_left] at e2`. Rewrite `e2` using `[Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (q i).2), Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (q' i).2)]`.

Conclude with `Fin.ext (by exact_mod_cast e2)`. Use `⟨fun i => ⟨(B β i % k).toNat, ?_⟩, B.symm (fun i => B β i / k), ?_⟩` and prove the remaining obligations. Use `Int.emod_lt_of_pos (B β i) hk'` as an intermediate fact. Use `Int.emod_nonneg (B β i) hk'.ne'` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Apply `B.injective` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Simplify using `only [map_add, map_nsmul, LinearEquiv.apply_symm_apply, Pi.add_apply, Pi.smul_apply]`. Rewrite using `[nsmul_eq_mul, Int.toNat_of_nonneg (Int.emod_nonneg _ hk'.ne')]`. Conclude with `Int.emod_add_mul_ediv _ _`.

Apply `B.injective` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Establish `e` using `congrFun (congrArg B h) i`. Simplify using `only [map_nsmul, Pi.smul_apply, nsmul_eq_mul] at e`. Conclude with `mul_left_cancel₀ hk'.ne' e`.
-/
theorem exists_class_reps (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : ℕ)
    (hk : 1 ≤ k) : ∃ ρ : (Fin (Module.finrank ℤ X) → Fin k) → X,
      (∀ q q' mu, ρ q + k • mu = ρ q' → q = q') ∧ (∀ β, ∃ q mu, ρ q + k • mu = β) ∧
      ∀ a b : X, k • a = k • b → a = b := by
  let B := (Module.finBasis ℤ X).equivFun
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  refine ⟨fun q => B.symm (fun i => ((q i : ℕ) : ℤ)), fun q q' mu h => ?_, fun β => ?_, fun a b h => ?_⟩
  · funext i
    have e := congrFun (congrArg B h) i
    simp only [map_add, map_nsmul, LinearEquiv.apply_symm_apply, Pi.add_apply, Pi.smul_apply] at e
    rw [nsmul_eq_mul] at e
    have e2 := congrArg (· % (k : ℤ)) e
    simp only [Int.add_mul_emod_self_left] at e2
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (q i).2),
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (q' i).2)] at e2
    exact Fin.ext (by exact_mod_cast e2)
  · refine ⟨fun i => ⟨(B β i % k).toNat, ?_⟩, B.symm (fun i => B β i / k), ?_⟩
    · have := Int.emod_lt_of_pos (B β i) hk'
      have := Int.emod_nonneg (B β i) hk'.ne'
      omega
    · apply B.injective
      funext i
      simp only [map_add, map_nsmul, LinearEquiv.apply_symm_apply, Pi.add_apply, Pi.smul_apply]
      rw [nsmul_eq_mul, Int.toNat_of_nonneg (Int.emod_nonneg _ hk'.ne')]
      exact Int.emod_add_mul_ediv _ _
  · apply B.injective
    funext i
    have e := congrFun (congrArg B h) i
    simp only [map_nsmul, Pi.smul_apply, nsmul_eq_mul] at e
    exact mul_left_cancel₀ hk'.ne' e

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
  [Algebra (FractionRing R) F] {k : ℕ}

/- English proof (translation)
Establish `hL` using `D.P.isLB`. Take `⟨u, hu, hc⟩` from `(gen_fe (D := D) (F := F) hG k mu ρ).1`. Use `sec_ext_val hL (fun y J hJ => ?_) j` and prove the remaining obligations. Rewrite using `[(secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (s.fe mu ρ u hu hc) _ _ y J hJ, (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (t.fe mu ρ u hu hc) _ _ y J hJ, h]`.
-/
theorem fam_term_eq (hG : GlobalFnsSt) {s t : Fam D F k} {ρ : D.X} (h : s.s ρ = t.s ρ) (mu : D.X) (j) :
    (s.s (ρ + k • mu)).f j = (t.s (ρ + k • mu)).f j := by
  have hL := D.P.isLB
  obtain ⟨u, hu, hc⟩ := (gen_fe (D := D) (F := F) hG k mu ρ).1
  refine sec_ext_val hL (fun y J hJ => ?_) j
  rw [(secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (s.fe mu ρ u hu hc) _ _ y J hJ,
    (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (t.fe mu ρ u hu hc) _ _ y J hJ, h]

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simp only [Finset.sum_empty, zero_f]`. Consider the case `insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_f, smul_f, ih]`.
-/
theorem sum_smul_f {I : Type} (S : Finset I) (c : I → F) (e : I → Fam D F k) (α : D.X) (j) :
    ((∑ x ∈ S, c x • e x).s α).f j = ∑ x ∈ S, resTop _ (gF D F (c x)) * ((e x).s α).f j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, zero_f]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_f, smul_f, ih]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `fin_cases i`. Conclude with `(Category.comp_id _).symm`. Use `show (padd D.P.A _ _).left = (snd (TF (R := R) F) D.P.A ≫ padd D.P.A _ _).left`. Use `congr 1`.

Simplify using `only [padd, comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]`. Use `show (toUnit (DegPre.BF D F) ≫ D.c α).left = (snd (TF (R := R) F) D.P.A ≫ toUnit _ ≫ D.c α).left`. Rewrite using `[comp_toUnit_assoc]`. Use `show (toUnit (DegPre.BF D F) ≫ η[D.P.A]).left = (snd (TF (R := R) F) D.P.A ≫ toUnit _ ≫ η[D.P.A]).left`. Rewrite using `[comp_toUnit_assoc]`.
-/
theorem famφ_eq (α : D.X) :
    DegPre.famφ D F α = fun i => (snd (TF (R := R) F) D.P.A).left ≫ DegPre.famφB D α i := by
  funext i
  fin_cases i
  · exact (Category.comp_id _).symm
  · show (padd D.P.A _ _).left = (snd (TF (R := R) F) D.P.A ≫ padd D.P.A _ _).left
    congr 1
    simp only [padd, comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
  · show (toUnit (DegPre.BF D F) ≫ D.c α).left = (snd (TF (R := R) F) D.P.A ≫ toUnit _ ≫ D.c α).left
    rw [comp_toUnit_assoc]
  · show (toUnit (DegPre.BF D F) ≫ η[D.P.A]).left = (snd (TF (R := R) F) D.P.A ≫ toUnit _ ≫ η[D.P.A]).left
    rw [comp_toUnit_assoc]

/- English proof (translation)
Set `f : R →+* F` to `(algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))`. Establish `key : ∀ (t : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R)), t = Spec.map (CommRingCat.ofHom f) → ∀ φ : Fin 4 → ((Over.mk t ⊗ D.P.A).left ⟶ D.P.A.left), φ = (fun i => (snd (Over.mk t) D.P.A).left ≫ DegPre.famφB D α i) → ∃ b : Fin (k ^ D.P.g) → LB.Sec (LB.LinComb D.P.L φ (DegP …` using `Over.mk t) (A := D.P.A) _ b := by`. Introduce and unpack `t rfl φ rfl`. Take `⟨b, hb⟩` from `GlobalTheory.T.exists_twist_basis_off_prime hP hG hT R D hW ⊥ k hk α`. Use `⟨fun i => pullSec D.P.L (DegPre.famφB D α) (DegPre.famε k) (b i) _, hb F f (fun s hs => ?_) _ (fun i j => rfl)⟩` and prove the remaining obligations.

Use `IsUnit.mk0 _ fun h0 => hs ?_` and prove the remaining obligations. Establish `h1 : algebraMap R (FractionRing R) s = 0` using `(algebraMap (FractionRing R) F).injective (h0.trans (map_zero _).symm)`. Conclude with `(IsFractionRing.to_map_eq_zero_iff (K := FractionRing R)).1 h1`. Take `⟨b, hb⟩` from `key (jFK (R := R) F ≫ jK R) (by`. Simplify using `only [jFK, jK, f, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) _ (famφ_eq α)`.

Use `⟨b, fun s => ?_⟩` and prove the remaining obligations. Take `⟨r, hr, hu⟩` from `hb s`. Set `e` to `(Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv`. Use `⟨fun i => e (r i), fun j => (hr j).trans (Finset.sum_congr rfl fun i _ => ?_), fun c hc => ?_⟩` and prove the remaining obligations. Use `congr 2 show _ = (fst (TF (R := R) F) D.P.A).left.appTop.hom (e.symm (e (r i)))`.

Rewrite using `[e.symm_apply_apply]`. Use `hu (fun i => e.symm (c i)) hc` as an intermediate fact. Use function extensionality and compare the values at `i`. Rewrite using `[← this]`. Conclude with `(e.apply_symm_apply _).symm`.
-/
theorem exists_term_basis (hG : GlobalFnsSt) (hP : PolBaseChangeSt) (hT : TwistBaseChangeStatement)
    [IsNoetherianRing R]
    (hW : ∃ W : (Spec (CommRingCat.of R)).Opens, genericPoint (Spec (CommRingCat.of R)) ∈ W ∧ Nonempty (PsiOn D W))
    (hk : 1 ≤ k) (α : D.X) :
    ∃ b : Fin (k ^ D.P.g) → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)),
      ∀ s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)),
        ∃! c : Fin (k ^ D.P.g) → F, ∀ j, s.f j = ∑ i, resTop _ (gF D F (c i)) * (b i).f j := by
  let f : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))
  have key : ∀ (t : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R)), t = Spec.map (CommRingCat.ofHom f) →
      ∀ φ : Fin 4 → ((Over.mk t ⊗ D.P.A).left ⟶ D.P.A.left),
        φ = (fun i => (snd (Over.mk t) D.P.A).left ≫ DegPre.famφB D α i) →
      ∃ b : Fin (k ^ D.P.g) → LB.Sec (LB.LinComb D.P.L φ (DegPre.famε k)),
        IsSecBasis (T := Over.mk t) (A := D.P.A) _ b := by
    rintro t rfl φ rfl
    obtain ⟨b, hb⟩ := GlobalTheory.T.exists_twist_basis_off_prime hP hG hT R D hW ⊥ k hk α
    refine ⟨fun i => pullSec D.P.L (DegPre.famφB D α) (DegPre.famε k) (b i) _, hb F f (fun s hs => ?_) _
      (fun i j => rfl)⟩
    refine IsUnit.mk0 _ fun h0 => hs ?_
    have h1 : algebraMap R (FractionRing R) s = 0 := (algebraMap (FractionRing R) F).injective (h0.trans (map_zero _).symm)
    exact (IsFractionRing.to_map_eq_zero_iff (K := FractionRing R)).1 h1
  obtain ⟨b, hb⟩ := key (jFK (R := R) F ≫ jK R) (by
    simp only [jFK, jK, f, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) _ (famφ_eq α)
  refine ⟨b, fun s => ?_⟩
  obtain ⟨r, hr, hu⟩ := hb s
  let e := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv
  refine ⟨fun i => e (r i), fun j => (hr j).trans (Finset.sum_congr rfl fun i _ => ?_), fun c hc => ?_⟩
  · congr 2
    show _ = (fst (TF (R := R) F) D.P.A).left.appTop.hom (e.symm (e (r i)))
    rw [e.symm_apply_apply]
  · have := hu (fun i => e.symm (c i)) hc
    funext i
    rw [← this]
    exact (e.apply_symm_apply _).symm

/- English proof (translation)
Introduce `hG hP hT R _ _ _ D hB hW F _ _ k hk`. Take `⟨ρ, hρ, hsurj, hcan⟩` from `exists_class_reps D.X k hk`. Use `choose b hb using fun α => exists_term_basis (D := D) (F := F) hG hP hT hW hk α`. Use `choose e he he0 using fun x : (Fin D.rank → Fin k) × Fin (k ^ D.P.g) => UUA.exists_fam_rep (F := F) hG hB k (ρ x.1) (fun a c h => hcan a c (add_left_cancel h)) (b (ρ x.1) x.2)`. Establish `ev : ∀ (c : (Fin D.rank → Fin k) × Fin (k ^ D.P.g) → F) q j, ((∑ x, c x • e x).s (ρ q)).f j = ∑ i, resTop _ (gF D F (c (q, i))) * (b (ρ q) i).f j`.

Introduce `c q j`. Rewrite using `[sum_smul_f, Fintype.sum_prod_type, Finset.sum_eq_single q]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [he (q, i)]`. Introduce `q' _ hq`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[he0 (q', i) (ρ q) (fun mu h => hq (hρ _ _ _ h)) j, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ q) h`. Establish `hli : LinearIndependent F e`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce and unpack `c hc ⟨q, i⟩`. Establish `h1` using `(hb (ρ q) SecOps.secZero).unique (y₁ := fun i => c (q, i)) (y₂ := fun _ => 0) (fun j => by rw [← ev, hc]; rfl) (fun j => by simp only [map_zero, resTop, zero_mul, Finset.sum_const_zero]; rfl)`. Conclude with `congrFun h1 i`. Establish `hsp : ⊤ ≤ Submodule.span F (Set.range e)`. Introduce `s _`.

Use `choose c hc using fun q => (hb (ρ q) (s.s (ρ q))).exists`. Use `(Submodule.mem_span_range_iff_exists_fun F).2 ⟨fun x => c x.1 x.2, fam_ext fun β j => ?_⟩` and prove the remaining obligations. Take `⟨q, mu, rfl⟩` from `hsurj β`. Use `fam_term_eq hG (SecOps.sec_ext fun j' => ?_) mu j` and prove the remaining obligations. Rewrite using `[ev (fun x => c x.1 x.2) q j', hc q j']`.

Set `B` to `Module.Basis.mk hli hsp`. Use `⟨Module.Finite.of_basis B, ?_⟩` and prove the remaining obligations. Rewrite using `[Module.finrank_eq_card_basis B, pow_add]`. Simplify using the standard rewrite rules.
-/
theorem finrank_fam : GlobalFnsSt → PolBaseChangeSt → DVR.TwistBaseChangeStatement → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R), D.TauBimult → (∃ W : (Spec (CommRingCat.of R)).Opens, genericPoint (Spec (CommRingCat.of R)) ∈ W ∧ Nonempty (PsiOn D W)) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → Module.Finite F (Fam D F k) ∧ Module.finrank F (Fam D F k) = k ^ (D.rank + D.P.g) := by
  intro hG hP hT R _ _ _ D hB hW F _ _ k hk
  classical
  obtain ⟨ρ, hρ, hsurj, hcan⟩ := exists_class_reps D.X k hk
  choose b hb using fun α => exists_term_basis (D := D) (F := F) hG hP hT hW hk α
  choose e he he0 using fun x : (Fin D.rank → Fin k) × Fin (k ^ D.P.g) =>
    UUA.exists_fam_rep (F := F) hG hB k (ρ x.1) (fun a c h => hcan a c (add_left_cancel h)) (b (ρ x.1) x.2)
  have ev : ∀ (c : (Fin D.rank → Fin k) × Fin (k ^ D.P.g) → F) q j,
      ((∑ x, c x • e x).s (ρ q)).f j = ∑ i, resTop _ (gF D F (c (q, i))) * (b (ρ q) i).f j := by
    intro c q j
    rw [sum_smul_f, Fintype.sum_prod_type, Finset.sum_eq_single q]
    · exact Finset.sum_congr rfl fun i _ => by rw [he (q, i)]
    · intro q' _ hq
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [he0 (q', i) (ρ q) (fun mu h => hq (hρ _ _ _ h)) j, mul_zero]
    · intro h; exact absurd (Finset.mem_univ q) h
  have hli : LinearIndependent F e := by
    rw [Fintype.linearIndependent_iff]
    rintro c hc ⟨q, i⟩
    have h1 := (hb (ρ q) SecOps.secZero).unique (y₁ := fun i => c (q, i)) (y₂ := fun _ => 0)
      (fun j => by rw [← ev, hc]; rfl)
      (fun j => by simp only [map_zero, resTop, zero_mul, Finset.sum_const_zero]; rfl)
    exact congrFun h1 i
  have hsp : ⊤ ≤ Submodule.span F (Set.range e) := by
    intro s _
    choose c hc using fun q => (hb (ρ q) (s.s (ρ q))).exists
    refine (Submodule.mem_span_range_iff_exists_fun F).2 ⟨fun x => c x.1 x.2, fam_ext fun β j => ?_⟩
    obtain ⟨q, mu, rfl⟩ := hsurj β
    refine fam_term_eq hG (SecOps.sec_ext fun j' => ?_) mu j
    rw [ev (fun x => c x.1 x.2) q j', hc q j']
  let B := Module.Basis.mk hli hsp
  refine ⟨Module.Finite.of_basis B, ?_⟩
  rw [Module.finrank_eq_card_basis B, pow_add]
  simp

end GlobalTheory.FamDim
