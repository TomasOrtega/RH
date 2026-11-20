import Development.EtaleCohomology.TateTwists.ExistsEtaleMonoMuTwistQuotientOfRootListsLocally
import Development.EtaleCohomology.TateTwists.EtaleTorsionCohomologyPrimaryLocalization
import Development.EtaleCohomology.TateTwists.EtaleTorsionCohomologyPrimaryPartBasic
import Development.EtaleCohomology.TateTwists.EtaleTorsionCohomologyLocalizationBasic

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.MuListPf

/- English proof (translation)
Apply `ULift.ext` to reduce the goal to its premises. Use `show ((a.val : ℕ) : ULift.{1} (ZMod q)).down = a`. Rewrite using `[ULift.down_natCast]`. Conclude with `ZMod.natCast_zmod_val a`.
-/
theorem ulift_natCast (q : ℕ) [NeZero q] (a : ZMod q) :
    ((a.val : ℕ) : ULift.{1} (ZMod q)) = ULift.up a := by
  apply ULift.ext
  show ((a.val : ℕ) : ULift.{1} (ZMod q)).down = a
  rw [ULift.down_natCast]
  exact ZMod.natCast_zmod_val a

/- English proof (translation)
Establish `hm : Finsupp.single ξ (1 : ULift.{1} (ZMod q)) - Finsupp.single ζ (ULift.up ((a ^ (1 : ℤ) : (ZMod q)ˣ) : ZMod q)) ∈ twRel q 1 B` using `Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩`. Establish `h2` using `(Submodule.Quotient.eq (twRel q 1 B)).2 hm`. Simplify using `only [zpow_one] at h2`. Rewrite using `[← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), ulift_natCast]`. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk _ = _`.

Rewrite using `[h2]`. Express the relevant statement in the definitionally equal form `_ = (ULift.up (a : ZMod q) : ULift.{1} (ZMod q)) • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Prim q B →₀ ULift.{1} (ZMod q)) ⧸ twRel q 1 B)`. Rewrite using `[← Submodule.Quotient.mk_smul, Finsupp.smul_single]`. Use `congr 2`. Conclude with `(mul_one _).symm`.
-/
theorem twGen_rel (q : ℕ) [NeZero q] (B : CommRingCat.{0}) (ζ ξ : Prim q B) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    twGenR B ξ = (a : ZMod q).val • twGenR B ζ := by
  have hm : Finsupp.single ξ (1 : ULift.{1} (ZMod q)) -
      Finsupp.single ζ (ULift.up ((a ^ (1 : ℤ) : (ZMod q)ˣ) : ZMod q)) ∈ twRel q 1 B :=
    Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩
  have h2 := (Submodule.Quotient.eq (twRel q 1 B)).2 hm
  simp only [zpow_one] at h2
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), ulift_natCast]
  change Submodule.Quotient.mk _ = _
  rw [h2]
  change _ = (ULift.up (a : ZMod q) : ULift.{1} (ZMod q)) •
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Prim q B →₀ ULift.{1} (ZMod q)) ⧸ twRel q 1 B)
  rw [← Submodule.Quotient.mk_smul, Finsupp.smul_single]
  congr 2
  exact (mul_one _).symm

/- English proof (translation)
Take `⟨-, -, h3, -, -, -⟩` from `LateralTheory.Fin.PrimitiveRootsOfUnityBasicIdentities.intersectionNumber_baseChange q B`. Assume the negation of the conclusion as `hn`. Use `h3 ζ n 0 (by rwa [Nat.modEq_zero_iff_dvd])` as an intermediate fact. Rewrite `this` using `[h, pow_zero, sub_self]`. Conclude with `not_isUnit_zero this`.
-/
theorem dvd_of_pow (q : ℕ) [NeZero q] (B : Type) [CommRing B] [Nontrivial B] (ζ : Prim q B) (n : ℕ)
    (h : ζ.1 ^ n = 1) : q ∣ n := by
  obtain ⟨-, -, h3, -, -, -⟩ := LateralTheory.Fin.PrimitiveRootsOfUnityBasicIdentities.intersectionNumber_baseChange q B
  by_contra hn
  have := h3 ζ n 0 (by rwa [Nat.modEq_zero_iff_dvd])
  rw [h, pow_zero, sub_self] at this
  exact not_isUnit_zero this

/- English proof (translation)
The claim follows from `| [], _ => ⟨0, by simp, by simp⟩ | ξ :: l, h => by obtain ⟨n, h1, h2⟩ := sum_eq q B ζ l (fun x hx => h x (List.mem_cons_of_mem _ hx)) obtain ⟨a, ha⟩ := h ξ List.mem_cons_self refine ⟨(a : ZMod q).val + n, ?_, ?_⟩ · simp only [List.map_cons, List.prod_cons, h1, ha, pow_add] · simp …`.
-/
theorem sum_eq (q : ℕ) [NeZero q] (B : CommRingCat.{0}) (ζ : Prim q B) : ∀ (l : List (Prim q B)),
    (∀ ξ ∈ l, ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val) →
    ∃ n : ℕ, (l.map fun ξ => ξ.1).prod = ζ.1 ^ n ∧ (l.map fun ξ => twGenR B ξ).sum = n • twGenR B ζ
  | [], _ => ⟨0, by simp, by simp⟩
  | ξ :: l, h => by
    obtain ⟨n, h1, h2⟩ := sum_eq q B ζ l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    obtain ⟨a, ha⟩ := h ξ List.mem_cons_self
    refine ⟨(a : ZMod q).val + n, ?_, ?_⟩
    · simp only [List.map_cons, List.prod_cons, h1, ha, pow_add]
    · simp only [List.map_cons, List.sum_cons, h2, twGen_rel q B ζ ξ a ha, add_smul]

/- English proof (translation)
The claim follows from `(V.presheaf.germ ⊤ x trivial).hom.domain_nontrivial`.
-/
theorem nontriv (V : Scheme.{0}) (x : V) : Nontrivial Γ(V, ⊤) :=
  (V.presheaf.germ ⊤ x trivial).hom.domain_nontrivial

/- English proof (translation)
Rewrite using `[← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]`. Establish `: ((n : ℕ) : ULift.{1} (ZMod q)) = 0`. Apply `ULift.ext` to reduce the goal to its premises. Rewrite using `[ULift.down_natCast]`. Conclude with `(ZMod.natCast_eq_zero_iff n q).2 hn`.

Rewrite using `[this, zero_smul]`.
-/
theorem zero_of_dvd (q : ℕ) [NeZero q] (M : Type*) [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (n : ℕ) (hn : q ∣ n) (x : M) : n • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((n : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext
    rw [ULift.down_natCast]
    exact (ZMod.natCast_eq_zero_iff n q).2 hn
  rw [this, zero_smul]

end LateralTheory.EtaleFoundations.MuListPf

namespace LateralTheory.EtaleFoundations
open MuListPf

/- English proof (translation)
Introduce `q _ U l hl`. Take `⟨hL1, hL2, -, -, hL5, hL6, hL7⟩` from `LateralTheory.Fin.EtaleLocalPropertyBasicClosure.intersectionNumber_baseChange`. Establish `stab : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V), ((twF q 1).map g.appTop).hom (l.map fun ζ => twGenR Γ(U, ⊤) ζ).sum = 0 → ((twF q 1).map (k ≫ g).appTop).hom (l.map fun ζ => twGenR Γ(U, ⊤) ζ).sum = 0`. Introduce `V W g k h`. Rewrite using `[Scheme.Hom.comp_appTop, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, h, map_zero]`.

Consider the cases of `l with`. Consider the case `nil => exact hL1 _ _ fun V g => by simp`. Consider the case `cons ζ l'`. Establish `hloc : Loc U fun V g => ∀ ξ ∈ ζ :: l', ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val`. Use `hL6 U (Fin (ζ :: l').length) (fun i V g => ∃ a : (ZMod q)ˣ, g.appTop.hom ((ζ :: l').get i).1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) (fun i => ((LateralTheory.Fin.EtalePrimitiveRootsExistLocally.intersectionNumber_baseChange q U).2.1 ζ ((ζ :: l').get i)))` as an intermediate fact.

Use `hL2 _ _ _ this fun V g h ξ hξ => ?_` and prove the remaining obligations. Take `⟨i, rfl⟩` from `List.get_of_mem hξ`. Conclude with `h i`. Use `hL5 U _ (hL2 _ _ _ hloc fun V g h => ?_)` and prove the remaining obligations. Distinguish the cases in `hV : IsEmpty V`.

Conclude with `hL7 V _`. Rewrite `hV` using `[not_isEmpty_iff]`. Take `⟨x⟩` from `hV`. Use `nontriv V x` as an intermediate fact. Establish `key : ((twF q 1).map g.appTop).hom ((ζ :: l').map fun ζ => twGenR Γ(U, ⊤) ζ).sum = 0`.

Rewrite using `[map_list_sum, List.map_map]`. Establish `e : ((fun y => ((twF q 1).map g.appTop).hom y) ∘ fun ζ => twGenR Γ(U, ⊤) ζ) = (fun ξ => twGenR Γ(V, ⊤) ξ) ∘ Prim.map g.appTop.hom`. Use function extensionality and compare the values at `ξ`. Conclude with `muK_gen_map q g.appTop ξ`. Rewrite using `[e, ← List.map_map]`.

Take `⟨n, h1, h2⟩` from `sum_eq q Γ(V, ⊤) (ζ.map g.appTop.hom) ((ζ :: l').map (Prim.map g.appTop.hom)) (by`. Introduce `ξ' hξ'`. Take `⟨ξ, hξ, rfl⟩` from `List.mem_map.1 hξ'`. Conclude with `h ξ hξ)`. Rewrite using `[h2]`.

Apply `zero_of_dvd q` to reduce the goal to its premises. Apply `dvd_of_pow q Γ(V, ⊤) (ζ.map g.appTop.hom) n` to reduce the goal to its premises. Rewrite using `[← h1]`. Use `Eq.trans ?_ ((congrArg g.appTop.hom hl).trans (map_one _))` and prove the remaining obligations. Rewrite using `[map_list_prod, List.map_map, List.map_map]`.

Both sides reduce to the same expression. Conclude with `hL1 _ _ fun W k => stab V W g k key`.
-/
theorem mu_root_list_product_one_sum_etale_locally_zero : MuRootListProductOneSumEtaleLocallyZero := by
  intro q _ U l hl
  obtain ⟨hL1, hL2, -, -, hL5, hL6, hL7⟩ := LateralTheory.Fin.EtaleLocalPropertyBasicClosure.intersectionNumber_baseChange
  have stab : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V),
      ((twF q 1).map g.appTop).hom (l.map fun ζ => twGenR Γ(U, ⊤) ζ).sum = 0 →
      ((twF q 1).map (k ≫ g).appTop).hom (l.map fun ζ => twGenR Γ(U, ⊤) ζ).sum = 0 := by
    intro V W g k h
    rw [Scheme.Hom.comp_appTop, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, h, map_zero]
  cases l with
  | nil => exact hL1 _ _ fun V g => by simp
  | cons ζ l' =>
    have hloc : Loc U fun V g => ∀ ξ ∈ ζ :: l', ∃ a : (ZMod q)ˣ,
        g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val := by
      have := hL6 U (Fin (ζ :: l').length) (fun i V g => ∃ a : (ZMod q)ˣ,
          g.appTop.hom ((ζ :: l').get i).1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val)
        (fun i => ((LateralTheory.Fin.EtalePrimitiveRootsExistLocally.intersectionNumber_baseChange q U).2.1 ζ ((ζ :: l').get i)))
      refine hL2 _ _ _ this fun V g h ξ hξ => ?_
      obtain ⟨i, rfl⟩ := List.get_of_mem hξ
      exact h i
    refine hL5 U _ (hL2 _ _ _ hloc fun V g h => ?_)
    by_cases hV : IsEmpty V
    · exact hL7 V _
    · rw [not_isEmpty_iff] at hV
      obtain ⟨x⟩ := hV
      have := nontriv V x
      have key : ((twF q 1).map g.appTop).hom ((ζ :: l').map fun ζ => twGenR Γ(U, ⊤) ζ).sum = 0 := by
        rw [map_list_sum, List.map_map]
        have e : ((fun y => ((twF q 1).map g.appTop).hom y) ∘ fun ζ => twGenR Γ(U, ⊤) ζ) =
            (fun ξ => twGenR Γ(V, ⊤) ξ) ∘ Prim.map g.appTop.hom := by
          funext ξ; exact muK_gen_map q g.appTop ξ
        rw [e, ← List.map_map]
        obtain ⟨n, h1, h2⟩ := sum_eq q Γ(V, ⊤) (ζ.map g.appTop.hom) ((ζ :: l').map (Prim.map g.appTop.hom))
          (by
            intro ξ' hξ'
            obtain ⟨ξ, hξ, rfl⟩ := List.mem_map.1 hξ'
            exact h ξ hξ)
        rw [h2]
        apply zero_of_dvd q
        apply dvd_of_pow q Γ(V, ⊤) (ζ.map g.appTop.hom) n
        rw [← h1]
        refine Eq.trans ?_ ((congrArg g.appTop.hom hl).trans (map_one _))
        rw [map_list_prod, List.map_map, List.map_map]
        rfl
      exact hL1 _ _ fun W k => stab V W g k key

end LateralTheory.EtaleFoundations
