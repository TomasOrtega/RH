import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentConstPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeBaseChangeOfIdem
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingHenselianAndSmoothPointsLift
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.ConnConstSplit

open IsLocalRing

/- English proof (translation)
Establish `key : ∀ M : Ideal A, M.IsMaximal → M = RingHom.ker c₀`. Introduce `M hM`. Establish `hu : (M.under O).IsMaximal` using `Ideal.IsMaximal.under O M`. Establish `hum : M.under O = maximalIdeal O` using `IsLocalRing.eq_maximalIdeal hu`. Use `letI : Field (A ⧸ M) := Ideal.Quotient.field M`.

Set `g : O →+* A ⧸ M` to `(Ideal.Quotient.mk M).comp (algebraMap O A)`. Use `haveI : IsLocalHom g := ⟨fun x hx => by`. Assume the negation of the conclusion as `h`. Establish `hxm : x ∈ M.under O` using `by rw [hum]; exact h`. Establish `h0 : g x = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 hxm`.

Conclude with `hx.ne_zero h0⟩`. Set `f : ResidueField O →+* A ⧸ M` to `ResidueField.lift g`. Use `letI : Algebra (ResidueField O) (A ⧸ M) := f.toAlgebra`. Establish `hf : ∀ x : O, f (residue O x) = g x` using `fun x => rfl`. Use `haveI : Algebra.IsIntegral (ResidueField O) (A ⧸ M) := ⟨fun y => by`.

Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Take `⟨P, hPm, hPa⟩` from `Algebra.IsIntegral.isIntegral (R := O) a`. Use `⟨P.map (residue O), hPm.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map]`. Establish `h1 : (algebraMap (ResidueField O) (A ⧸ M)).comp (residue O) = g` using `RingHom.ext hf`.

Rewrite using `[h1]`. Establish `h2` using `Polynomial.hom_eval₂ P (algebraMap O A) (Ideal.Quotient.mk M) a`. Rewrite `h2` using `[hPa, map_zero]`. Conclude with `h2.symm⟩`. Establish `hsurj` using `(IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ResidueField O) (K := A ⧸ M)).2`.

Set `e : ResidueField O ≃+* A ⧸ M` to `RingEquiv.ofBijective f ⟨f.injective, hsurj⟩`. Set `c : A →ₐ[O] ResidueField O` to `{ toRingHom := e.symm.toRingHom.comp (Ideal.Quotient.mk M) commutes' := fun x => by`. Express the relevant statement in the definitionally equal form `e.symm (Ideal.Quotient.mk M (algebraMap O A x)) = algebraMap O (ResidueField O) x`. Rewrite using `[RingEquiv.symm_apply_eq]`. Conclude with `(hf x).symm }`.

Establish `hc : c = c₀` using `Subsingleton.elim _ _`. Use extensionality with `a`. Rewrite using `[← hc, RingHom.mem_ker]`. Express the relevant statement in the definitionally equal form `a ∈ M ↔ e.symm (Ideal.Quotient.mk M a) = 0`. Rewrite using `[RingEquiv.symm_apply_eq, map_zero, Ideal.Quotient.eq_zero_iff_mem]`.

Use `haveI : Nontrivial A := c₀.toRingHom.domain_nontrivial`. Take `⟨M, hM⟩` from `Ideal.exists_maximal A`. Conclude with `IsLocalRing.of_unique_max_ideal ⟨M, hM, fun M' hM' => (key M' hM').trans (key M hM).symm⟩`.
-/
theorem isLocalRing_of_subsingleton_points (O : Type) [CommRing O] [IsLocalRing O]
    [IsAlgClosed (ResidueField O)] (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A]
    [Subsingleton (A →ₐ[O] ResidueField O)] (c₀ : A →ₐ[O] ResidueField O) : IsLocalRing A := by
  have key : ∀ M : Ideal A, M.IsMaximal → M = RingHom.ker c₀ := by
    intro M hM
    have hu : (M.under O).IsMaximal := Ideal.IsMaximal.under O M
    have hum : M.under O = maximalIdeal O := IsLocalRing.eq_maximalIdeal hu
    letI : Field (A ⧸ M) := Ideal.Quotient.field M
    let g : O →+* A ⧸ M := (Ideal.Quotient.mk M).comp (algebraMap O A)
    haveI : IsLocalHom g := ⟨fun x hx => by
      by_contra h
      have hxm : x ∈ M.under O := by rw [hum]; exact h
      have h0 : g x = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hxm
      exact hx.ne_zero h0⟩
    let f : ResidueField O →+* A ⧸ M := ResidueField.lift g
    letI : Algebra (ResidueField O) (A ⧸ M) := f.toAlgebra
    have hf : ∀ x : O, f (residue O x) = g x := fun x => rfl
    haveI : Algebra.IsIntegral (ResidueField O) (A ⧸ M) := ⟨fun y => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨P, hPm, hPa⟩ := Algebra.IsIntegral.isIntegral (R := O) a
      refine ⟨P.map (residue O), hPm.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have h1 : (algebraMap (ResidueField O) (A ⧸ M)).comp (residue O) = g := RingHom.ext hf
      rw [h1]
      have h2 := Polynomial.hom_eval₂ P (algebraMap O A) (Ideal.Quotient.mk M) a
      rw [hPa, map_zero] at h2
      exact h2.symm⟩
    have hsurj := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ResidueField O) (K := A ⧸ M)).2
    let e : ResidueField O ≃+* A ⧸ M := RingEquiv.ofBijective f ⟨f.injective, hsurj⟩
    let c : A →ₐ[O] ResidueField O :=
      { toRingHom := e.symm.toRingHom.comp (Ideal.Quotient.mk M)
        commutes' := fun x => by
          change e.symm (Ideal.Quotient.mk M (algebraMap O A x)) = algebraMap O (ResidueField O) x
          rw [RingEquiv.symm_apply_eq]
          exact (hf x).symm }
    have hc : c = c₀ := Subsingleton.elim _ _
    ext a
    rw [← hc, RingHom.mem_ker]
    change a ∈ M ↔ e.symm (Ideal.Quotient.mk M a) = 0
    rw [RingEquiv.symm_apply_eq, map_zero, Ideal.Quotient.eq_zero_iff_mem]
  haveI : Nontrivial A := c₀.toRingHom.domain_nontrivial
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  exact IsLocalRing.of_unique_max_ideal ⟨M, hM, fun M' hM' => (key M' hM').trans (key M hM).symm⟩

/- English proof (translation)
The claim follows from `congrArg WithConv.ofConv (map_mul ((GlobalTheory.PDiv.ptsPush (H.A n) x).comp GlobalTheory.PDiv.toPts) (f.conv n) (g.conv n))`.
-/
theorem comp_add_app {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {B : Type} [CommRing B]
    [Algebra O B] {G H : PDivGroup p O} (f g : G ⟶ H) (n : ℕ) (x : G.A n →ₐ[O] B) :
    x.comp ((f + g).app n : H.A n →ₐ[O] G.A n) = WithConv.ofConv
      (WithConv.toConv (x.comp (f.app n : H.A n →ₐ[O] G.A n)) *
        WithConv.toConv (x.comp (g.app n : H.A n →ₐ[O] G.A n))) :=
  congrArg WithConv.ofConv
    (map_mul ((GlobalTheory.PDiv.ptsPush (H.A n) x).comp GlobalTheory.PDiv.toPts) (f.conv n) (g.conv n))

/- English proof (translation)
Establish `hk : ∀ k : ℕ, y ^ (k + 1) = y`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact pow_one y`. Consider the case `succ k ih => rw [pow_succ, ih, hy]`.

Rewrite using `[← h, ← Nat.sub_add_cancel hm, hk]`.
-/
theorem eq_one_of_mul_self_of_pow {M : Type*} [Monoid M] {y : M} (hy : y * y = y) {m : ℕ}
    (hm : 1 ≤ m) (h : y ^ m = 1) : y = 1 := by
  have hk : ∀ k : ℕ, y ^ (k + 1) = y := by
    intro k
    induction k with
    | zero => exact pow_one y
    | succ k ih => rw [pow_succ, ih, hy]
  rw [← h, ← Nat.sub_add_cancel hm, hk]

end GlobalTheory.ConnConstSplit

namespace GlobalTheory.ConnConstSplit

open IsLocalRing

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ _ _ hv G`. Use `haveI := ValuationRing.of_integers v hv`. Use `haveI := hv.isFractionRing`. Use `haveI : IsAlgClosed (ResidueField O) := GlobalTheory.isAlgClosed_residueField_of_valuationRing_of_isAlgClosed O C`. Take `⟨u, huu, hfix, hrange⟩` from `GlobalTheory.ConstPart.exists_idempotent_constPart p C v O hv G`.

Take `⟨G₂, i₂, q₂, h₂1, h₂2⟩` from `GlobalTheory.PDivGroup.IdemSplit.idempotent_split_integers p C v O hv G u huu`. Establish `h1u : (𝟙 G - u) ≫ (𝟙 G - u) = 𝟙 G - u`. Simplify using `only [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Category.comp_id, huu]`. Normalize the expressions using the abelian group laws. Take `⟨G₁, i₁, q₁, h₁1, h₁2⟩` from `GlobalTheory.PDivGroup.IdemSplit.idempotent_split_integers p C v O hv G (𝟙 G - u) h1u`.

Establish `hl₁ : ∀ n (b : G₁.A n), i₁.app n (q₁.app n b) = b` using `fun n b => by`. Establish `h` using `congrArg (fun f : G₁ ⟶ G₁ => f.app n b) h₁1`. Simplify using `using h`. Establish `hl₂ : ∀ n (b : G₂.A n), i₂.app n (q₂.app n b) = b` using `fun n b => by`. Establish `h` using `congrArg (fun f : G₂ ⟶ G₂ => f.app n b) h₂1`.

Simplify using `using h`. Establish `hu₂ : ∀ n (a : G.A n), u.app n a = q₂.app n (i₂.app n a)` using `fun n a => by`. Rewrite using `[← h₂2]`. Both sides reduce to the same expression. Use `⟨G₁, G₂, ⟨i₁, i₂, q₁, q₂, h₁1, h₂1, ?_, ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations.

Establish `e1 : i₁ ≫ q₂ = i₁ ≫ ((q₁ ≫ i₁) ≫ (q₂ ≫ i₂)) ≫ q₂`. Simplify using `only [Category.assoc]`. Rewrite using `[h₂1, Category.comp_id, reassoc_of% h₁1]`. Rewrite using `[e1, h₁2, h₂2, Preadditive.sub_comp, Category.id_comp, huu, sub_self, Limits.zero_comp, Limits.comp_zero]`. Establish `e1 : i₂ ≫ q₁ = i₂ ≫ ((q₂ ≫ i₂) ≫ (q₁ ≫ i₁)) ≫ q₁`.

Simplify using `only [Category.assoc]`. Rewrite using `[h₁1, Category.comp_id, reassoc_of% h₂1]`. Rewrite using `[e1, h₁2, h₂2, Preadditive.comp_sub, Category.comp_id, huu, sub_self, Limits.zero_comp, Limits.comp_zero]`. Rewrite using `[h₁2, h₂2, sub_add_cancel]`. Introduce `n`.

Set `c₀ : G₁.A n →ₐ[O] ResidueField O` to `(Algebra.ofId O (ResidueField O)).comp (Bialgebra.counitAlgHom O (G₁.A n))`. Establish `hall : ∀ c : G₁.A n →ₐ[O] ResidueField O, c = c₀`. Introduce `c`. Use `set x : G.A n →ₐ[O] ResidueField O := c.comp (i₁.app n : G.A n →ₐ[O] G₁.A n) with hxdef`. Establish `hx1 : x.comp (u.app n : G.A n →ₐ[O] G.A n) = x` using `AlgHom.ext (hfix n x)`.

Establish `hx2 : x.comp ((q₁ ≫ i₁).app n : G.A n →ₐ[O] G.A n) = x` using `AlgHom.ext fun a => by`. Express the relevant statement in the definitionally equal form `c (i₁.app n (q₁.app n (i₁.app n a))) = c (i₁.app n a)`. Rewrite using `[hl₁]`. Establish `hsum : q₁ ≫ i₁ + u = 𝟙 G` using `by rw [h₁2, sub_add_cancel]`. Establish `hid : x.comp ((𝟙 G : G ⟶ G).app n : G.A n →ₐ[O] G.A n) = x` using `AlgHom.ext fun a => rfl`.

Establish `hmul` using `comp_add_app (q₁ ≫ i₁) u n x`. Rewrite `hmul` using `[hsum, hid, hx2, hx1]`. Establish `hyy : WithConv.toConv x * WithConv.toConv x = WithConv.toConv x`. Conclude with `(congrArg WithConv.toConv hmul).symm`. Establish `hx : WithConv.toConv x = 1` using `eq_one_of_mul_self_of_pow hyy (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos) (G.pts_pow_self n (WithConv.toConv x))`.

Use extensionality with `b`. Establish `hb : c b = x (q₁.app n b)`. Express the relevant statement in the definitionally equal form `c b = c (i₁.app n (q₁.app n b))`. Rewrite using `[hl₁]`. Rewrite using `[hb]`.

Establish `hx' : x = WithConv.ofConv (1 : WithConv (G.A n →ₐ[O] ResidueField O))`. Rewrite using `[← hx]`. Rewrite using `[hx', AlgHom.convOne_apply, CoalgHomClass.counit_comp_apply]`. Both sides reduce to the same expression. Use `haveI : Subsingleton (G₁.A n →ₐ[O] ResidueField O) := ⟨fun a b => (hall a).trans (hall b).symm⟩`.

Conclude with `isLocalRing_of_subsingleton_points O (G₁.A n) c₀`. Introduce `n`. Take `⟨N, ⟨e⟩⟩` from `hrange n`. Establish `hinj : Function.Injective (q₂.app n : G₂.A n →ₐ[O] G.A n)` using `fun a b h => by`. Rewrite using `[← hl₂ n a, ← hl₂ n b]`.

Conclude with `congrArg (i₂.app n) h`. Establish `hrng : (u.app n : G.A n →ₐ[O] G.A n).range = (q₂.app n : G₂.A n →ₐ[O] G.A n).range`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`.

Conclude with `⟨i₂.app n a, (hu₂ n a).symm⟩`. Introduce and unpack `⟨b, rfl⟩`. Use `⟨q₂.app n b, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `u.app n (q₂.app n b) = q₂.app n b`. Rewrite using `[hu₂, hl₂]`.

Set `e' : G₂.A n ≃ₐ[O] (Fin N → O)` to `(AlgEquiv.ofInjective _ hinj).trans ((Subalgebra.equivOfEq _ _ hrng.symm).trans e)`. Establish `hN : N = p ^ (n * G₂.height)`. Establish `h1` using `G₂.rank_eq n ⟨maximalIdeal O, inferInstance⟩`. Rewrite `h1` using `[Module.rankAtStalk_eq_of_equiv e'.toLinearEquiv, Module.rankAtStalk_eq_finrank_of_free, Module.finrank_fin_fun]`. Simplify using `using h1`.

Conclude with `⟨hN ▸ e'⟩`.
-/
theorem exists_isSum_conn_const : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O → ∀ G : PDivGroup p O, ∃ G₁ G₂ : PDivGroup p O, IsSum G G₁ G₂ ∧ PDivLat.IsConn G₁ ∧ IsConst G₂ := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ hv G
  haveI := ValuationRing.of_integers v hv
  haveI := hv.isFractionRing
  haveI : IsAlgClosed (ResidueField O) :=
    GlobalTheory.isAlgClosed_residueField_of_valuationRing_of_isAlgClosed O C
  obtain ⟨u, huu, hfix, hrange⟩ := GlobalTheory.ConstPart.exists_idempotent_constPart p C v O hv G
  obtain ⟨G₂, i₂, q₂, h₂1, h₂2⟩ := GlobalTheory.PDivGroup.IdemSplit.idempotent_split_integers p C v O hv G u huu
  have h1u : (𝟙 G - u) ≫ (𝟙 G - u) = 𝟙 G - u := by
    simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Category.comp_id, huu]
    abel
  obtain ⟨G₁, i₁, q₁, h₁1, h₁2⟩ := GlobalTheory.PDivGroup.IdemSplit.idempotent_split_integers p C v O hv G (𝟙 G - u) h1u
  have hl₁ : ∀ n (b : G₁.A n), i₁.app n (q₁.app n b) = b := fun n b => by
    have h := congrArg (fun f : G₁ ⟶ G₁ => f.app n b) h₁1
    simpa using h
  have hl₂ : ∀ n (b : G₂.A n), i₂.app n (q₂.app n b) = b := fun n b => by
    have h := congrArg (fun f : G₂ ⟶ G₂ => f.app n b) h₂1
    simpa using h
  have hu₂ : ∀ n (a : G.A n), u.app n a = q₂.app n (i₂.app n a) := fun n a => by
    rw [← h₂2]; rfl
  refine ⟨G₁, G₂, ⟨i₁, i₂, q₁, q₂, h₁1, h₂1, ?_, ?_, ?_⟩, ?_, ?_⟩
  · have e1 : i₁ ≫ q₂ = i₁ ≫ ((q₁ ≫ i₁) ≫ (q₂ ≫ i₂)) ≫ q₂ := by
      simp only [Category.assoc]
      rw [h₂1, Category.comp_id, reassoc_of% h₁1]
    rw [e1, h₁2, h₂2, Preadditive.sub_comp, Category.id_comp, huu, sub_self,
      Limits.zero_comp, Limits.comp_zero]
  · have e1 : i₂ ≫ q₁ = i₂ ≫ ((q₂ ≫ i₂) ≫ (q₁ ≫ i₁)) ≫ q₁ := by
      simp only [Category.assoc]
      rw [h₁1, Category.comp_id, reassoc_of% h₂1]
    rw [e1, h₁2, h₂2, Preadditive.comp_sub, Category.comp_id, huu, sub_self,
      Limits.zero_comp, Limits.comp_zero]
  · rw [h₁2, h₂2, sub_add_cancel]
  · intro n
    let c₀ : G₁.A n →ₐ[O] ResidueField O :=
      (Algebra.ofId O (ResidueField O)).comp (Bialgebra.counitAlgHom O (G₁.A n))
    have hall : ∀ c : G₁.A n →ₐ[O] ResidueField O, c = c₀ := by
      intro c
      set x : G.A n →ₐ[O] ResidueField O := c.comp (i₁.app n : G.A n →ₐ[O] G₁.A n) with hxdef
      have hx1 : x.comp (u.app n : G.A n →ₐ[O] G.A n) = x := AlgHom.ext (hfix n x)
      have hx2 : x.comp ((q₁ ≫ i₁).app n : G.A n →ₐ[O] G.A n) = x := AlgHom.ext fun a => by
        change c (i₁.app n (q₁.app n (i₁.app n a))) = c (i₁.app n a)
        rw [hl₁]
      have hsum : q₁ ≫ i₁ + u = 𝟙 G := by rw [h₁2, sub_add_cancel]
      have hid : x.comp ((𝟙 G : G ⟶ G).app n : G.A n →ₐ[O] G.A n) = x := AlgHom.ext fun a => rfl
      have hmul := comp_add_app (q₁ ≫ i₁) u n x
      rw [hsum, hid, hx2, hx1] at hmul
      have hyy : WithConv.toConv x * WithConv.toConv x = WithConv.toConv x := by
        exact (congrArg WithConv.toConv hmul).symm
      have hx : WithConv.toConv x = 1 :=
        eq_one_of_mul_self_of_pow hyy (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)
          (G.pts_pow_self n (WithConv.toConv x))
      ext b
      have hb : c b = x (q₁.app n b) := by
        change c b = c (i₁.app n (q₁.app n b)); rw [hl₁]
      rw [hb]
      have hx' : x = WithConv.ofConv (1 : WithConv (G.A n →ₐ[O] ResidueField O)) := by
        rw [← hx]
      rw [hx', AlgHom.convOne_apply, CoalgHomClass.counit_comp_apply]
      rfl
    haveI : Subsingleton (G₁.A n →ₐ[O] ResidueField O) :=
      ⟨fun a b => (hall a).trans (hall b).symm⟩
    exact isLocalRing_of_subsingleton_points O (G₁.A n) c₀
  · intro n
    obtain ⟨N, ⟨e⟩⟩ := hrange n
    have hinj : Function.Injective (q₂.app n : G₂.A n →ₐ[O] G.A n) := fun a b h => by
      rw [← hl₂ n a, ← hl₂ n b]
      exact congrArg (i₂.app n) h
    have hrng : (u.app n : G.A n →ₐ[O] G.A n).range = (q₂.app n : G₂.A n →ₐ[O] G.A n).range := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨i₂.app n a, (hu₂ n a).symm⟩
      · rintro ⟨b, rfl⟩
        refine ⟨q₂.app n b, ?_⟩
        change u.app n (q₂.app n b) = q₂.app n b
        rw [hu₂, hl₂]
    let e' : G₂.A n ≃ₐ[O] (Fin N → O) :=
      (AlgEquiv.ofInjective _ hinj).trans ((Subalgebra.equivOfEq _ _ hrng.symm).trans e)
    have hN : N = p ^ (n * G₂.height) := by
      have h1 := G₂.rank_eq n ⟨maximalIdeal O, inferInstance⟩
      rw [Module.rankAtStalk_eq_of_equiv e'.toLinearEquiv, Module.rankAtStalk_eq_finrank_of_free,
        Module.finrank_fin_fun] at h1
      simpa using h1
    exact ⟨hN ▸ e'⟩

end GlobalTheory.ConnConstSplit
