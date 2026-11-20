import Mathlib
import GroundTheory.TateCohomology.HerbrandAbstract
import GroundTheory.GlobalFields.HerbrandQuotients.Cyclic

namespace GroundTheory.Global

open GroundTheory.GroupCoh MulAction

section Orbits

variable (G : Type*) {X : Type*} [Group G] [MulAction G X]

noncomputable def orbitPoint (x : X) : X :=
  Quotient.out (Quotient.mk (orbitRel G X) x)

variable {G}

/- English proof (translation)
The claim follows from `Quotient.out_eq _`.
-/
theorem mk_orbitPoint (x : X) :
    Quotient.mk (orbitRel G X) (orbitPoint G x) = Quotient.mk (orbitRel G X) x :=
  Quotient.out_eq _

/- English proof (translation)
The claim follows from `orbitRel_apply.1 (Quotient.exact (mk_orbitPoint x))`.
-/
theorem orbitPoint_mem (x : X) : orbitPoint G x ∈ orbit G x :=
  orbitRel_apply.1 (Quotient.exact (mk_orbitPoint x))

/- English proof (translation)
Unfold `orbitPoint`. Rewrite using `[Quotient.sound (orbitRel_apply.2 h)]`.
-/
theorem orbitPoint_eq_of_mem {x y : X} (h : y ∈ orbit G x) : orbitPoint G y = orbitPoint G x := by
  unfold orbitPoint
  rw [Quotient.sound (orbitRel_apply.2 h)]

/- English proof (translation)
The claim follows from `orbitPoint_eq_of_mem (mem_orbit x g)`.
-/
theorem orbitPoint_smul (g : G) (x : X) : orbitPoint G (g • x) = orbitPoint G x :=
  orbitPoint_eq_of_mem (mem_orbit x g)

/- English proof (translation)
The claim follows from `orbitPoint_eq_of_mem (orbitPoint_mem x)`.
-/
theorem orbitPoint_orbitPoint (x : X) : orbitPoint G (orbitPoint G x) = orbitPoint G x :=
  orbitPoint_eq_of_mem (orbitPoint_mem x)

/- English proof (translation)
Take `⟨g, rfl⟩` from `h`. Conclude with `(Nat.card_congr (stabilizerEquivStabilizer (rfl : g • x = g • x)).toEquiv).symm`.
-/
theorem card_stabilizer_eq_of_mem {x y : X} (h : y ∈ orbit G x) :
    Nat.card (stabilizer G y) = Nat.card (stabilizer G x) := by
  obtain ⟨g, rfl⟩ := h
  exact (Nat.card_congr (stabilizerEquivStabilizer (rfl : g • x = g • x)).toEquiv).symm

variable [Fintype G]

/- English proof (translation)
Establish `h1 : Nat.card (stabilizer G p) = (Finset.univ.filter fun g : G => g • p = p).card`. Rewrite using `[← Fintype.card_subtype, ← Nat.card_eq_fintype_card]`. Conclude with `Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_stabilizer_iff)`. Rewrite using `[h1]`. Use `Finset.card_bij' (fun g _ => g₀⁻¹ * g) (fun h _ => g₀ * h) ?_ ?_ ?_ ?_` and prove the remaining obligations.

Introduce `g hg`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢`. Rewrite using `[mul_smul, hg, inv_smul_smul]`. Introduce `h hh`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢`.

Rewrite using `[mul_smul, hh]`. Introduce `g _`. Simplify using the standard rewrite rules. Introduce `h _`. Simplify using the standard rewrite rules.
-/
theorem card_filter_smul_eq [DecidableEq X] (p : X) (g₀ : G) :
    (Finset.univ.filter fun g : G => g • p = g₀ • p).card = Nat.card (stabilizer G p) := by
  have h1 : Nat.card (stabilizer G p) = (Finset.univ.filter fun g : G => g • p = p).card := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_stabilizer_iff)
  rw [h1]
  refine Finset.card_bij' (fun g _ => g₀⁻¹ * g) (fun h _ => g₀ * h) ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    rw [mul_smul, hg, inv_smul_smul]
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
    rw [mul_smul, hh]
  · intro g _
    simp
  · intro h _
    simp

/- English proof (translation)
Distinguish the cases in `hy : y ∈ orbit G p`. Take `⟨g₀, rfl⟩` from `hy`. Rewrite using `[card_filter_smul_eq]`. Rewrite using `[Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun g _ hg => hy ⟨g, hg⟩)]`. Conclude with `dvd_zero _`.
-/
theorem card_stabilizer_dvd_card_filter [DecidableEq X] (p y : X) :
    Nat.card (stabilizer G p) ∣ (Finset.univ.filter fun g : G => g • p = y).card := by
  by_cases hy : y ∈ orbit G p
  · obtain ⟨g₀, rfl⟩ := hy
    rw [card_filter_smul_eq]
  · rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun g _ hg => hy ⟨g, hg⟩)]
    exact dvd_zero _

/- English proof (translation)
Use `Fintype.ofFinite X` as an intermediate fact. Rewrite using `[← Finset.sum_fiberwise Finset.univ (fun g : G => g • p) (fun g => F (g • p))]`. Use `Finset.dvd_sum fun y _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl fun g hg => by rw [(Finset.mem_filter.1 hg).2], Finset.sum_const, nsmul_eq_mul]`. Conclude with `Dvd.dvd.mul_right (Int.natCast_dvd_natCast.2 (card_stabilizer_dvd_card_filter p y)) _`.
-/
theorem card_stabilizer_dvd_sum [Finite X] (F : X → ℤ) (p : X) :
    (Nat.card (stabilizer G p) : ℤ) ∣ ∑ g : G, F (g • p) := by
  classical
  have := Fintype.ofFinite X
  rw [← Finset.sum_fiberwise Finset.univ (fun g : G => g • p) (fun g => F (g • p))]
  refine Finset.dvd_sum fun y _ => ?_
  rw [Finset.sum_congr rfl fun g hg => by rw [(Finset.mem_filter.1 hg).2], Finset.sum_const,
    nsmul_eq_mul]
  exact Dvd.dvd.mul_right (Int.natCast_dvd_natCast.2 (card_stabilizer_dvd_card_filter p y)) _

/- English proof (translation)
Establish `h1 : ∀ g : G, F (g • p) = if g • p = orbitPoint G p then F (orbitPoint G p) else 0`. Introduce `g`. Use `split_ifs with hg`. Rewrite using `[hg]`. Assume the negation of the conclusion as `hne`.

Apply `hg` to reduce the goal to its premises. Rewrite using `[← hF _ hne, orbitPoint_smul]`. Rewrite using `[Finset.sum_congr rfl fun g _ => h1 g, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]`. Take `⟨g₀, hg₀⟩` from `orbitPoint_mem (G := G) p`. Rewrite using `[← show g₀ • p = orbitPoint G p from hg₀, ← card_filter_smul_eq p g₀]`.
-/
theorem sum_smul_eq_of_support (F : X → ℤ) (hF : ∀ y, F y ≠ 0 → orbitPoint G y = y) (p : X) :
    ∑ g : G, F (g • p) = Nat.card (stabilizer G p) * F (orbitPoint G p) := by
  classical
  have h1 : ∀ g : G, F (g • p) = if g • p = orbitPoint G p then F (orbitPoint G p) else 0 := by
    intro g
    split_ifs with hg
    · rw [hg]
    · by_contra hne
      apply hg
      rw [← hF _ hne, orbitPoint_smul]
  rw [Finset.sum_congr rfl fun g _ => h1 g, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  obtain ⟨g₀, hg₀⟩ := orbitPoint_mem (G := G) p
  rw [← show g₀ • p = orbitPoint G p from hg₀, ← card_filter_smul_eq p g₀]

end Orbits

section Permutation

variable {G X : Type*} [Group G] [Fintype G] [MulAction G X]

/- English proof (translation)
Rewrite using `[normHom_apply, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]`. Simplify using `only [Representation.coeff_ofMulAction]`. Conclude with `Fintype.sum_equiv (Equiv.inv G) _ _ fun g => rfl`.
-/
theorem coeff_normHom_ofMulAction (f : MonoidAlgebra ℤ X) (p : X) :
    (normHom (Representation.ofMulAction ℤ G X) f).coeff p = ∑ g : G, f.coeff (g • p) := by
  rw [normHom_apply, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [Representation.coeff_ofMulAction]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ fun g => rfl

noncomputable def permOfFun [Finite X] (F : X → ℤ) : MonoidAlgebra ℤ X :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm F)

@[simp]
/- English proof (translation)
Simplify using `[permOfFun, MonoidAlgebra.coeff_ofCoeff]`.
-/
theorem coeff_permOfFun [Finite X] (F : X → ℤ) (x : X) : (permOfFun F).coeff x = F x := by
  simp [permOfFun, MonoidAlgebra.coeff_ofCoeff]

end Permutation

section Cohomology

variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X] {σ : G}

omit [Fintype G] [Finite X] in

/- English proof (translation)
Establish `h1` using `apply_eq_of_cycSub_eq_zero _ hσ (AddMonoidHom.mem_ker.1 hf) g⁻¹`. Establish `h2` using `congrArg (fun f : MonoidAlgebra ℤ X => f.coeff x) h1`. Simplify `h2` using `only [Representation.coeff_ofMulAction, inv_inv]`.
-/
theorem coeff_smul_of_mem_ker (hσ : ∀ g, g ∈ Subgroup.zpowers σ) {f : MonoidAlgebra ℤ X}
    (hf : f ∈ (cycSub (Representation.ofMulAction ℤ G X) σ).ker) (g : G) (x : X) :
    f.coeff (g • x) = f.coeff x := by
  have h1 := apply_eq_of_cycSub_eq_zero _ hσ (AddMonoidHom.mem_ker.1 hf) g⁻¹
  have h2 := congrArg (fun f : MonoidAlgebra ℤ X => f.coeff x) h1
  simpa only [Representation.coeff_ofMulAction, inv_inv] using h2

omit [Fintype G] in

/- English proof (translation)
Rewrite using `[AddMonoidHom.mem_ker, cycSub_apply]`. Use extensionality with `x`. Simplify using `[Representation.coeff_ofMulAction, hF]`.
-/
theorem permOfFun_mem_ker {F : X → ℤ} (hF : ∀ (g : G) x, F (g • x) = F x) :
    permOfFun F ∈ (cycSub (Representation.ofMulAction ℤ G X) σ).ker := by
  rw [AddMonoidHom.mem_ker, cycSub_apply]
  ext x
  simp [Representation.coeff_ofMulAction, hF]

/- English proof (translation)
Use `Fintype.ofFinite X` as an intermediate fact. Introduce `f hf`. Set `u : MonoidAlgebra ℤ X` to `∑ x, f.coeff x • MonoidAlgebra.single (orbitPoint G x) 1`. Establish `hcoeff_u : ∀ y, u.coeff y = ∑ x, if orbitPoint G x = y then f.coeff x else 0`. Introduce `y`.

Simplify using `[u, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]`. Establish `hfu : f - u ∈ (cycSub (Representation.ofMulAction ℤ G X) σ).range`. Establish `hf' : f - u = ∑ x, f.coeff x • (MonoidAlgebra.single x (1 : ℤ) - MonoidAlgebra.single (orbitPoint G x) 1)`. Use extensionality with `y`. Rewrite using `[MonoidAlgebra.coeff_sub, Finsupp.sub_apply, hcoeff_u]`.

Simplify using `[MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply, mul_sub, Finset.sum_sub_distrib]`. Rewrite using `[hf']`. Use `AddSubgroup.sum_mem _ fun x _ => AddSubgroup.zsmul_mem _ ?_ _` and prove the remaining obligations. Take `⟨g, hg⟩` from `orbitPoint_mem (G := G) x`. Establish `: MonoidAlgebra.single (orbitPoint G x) (1 : ℤ) = (Representation.ofMulAction ℤ G X) g (MonoidAlgebra.single x 1)`.

Rewrite using `[Representation.ofMulAction_single, ← show g • x = orbitPoint G x from hg]`. Rewrite using `[this, ← neg_sub]`. Conclude with `neg_mem (sub_mem_range_cycSub (Representation.ofMulAction ℤ G X) hσ g _)`. Establish `hNu : normHom (Representation.ofMulAction ℤ G X) u = 0`. Take `⟨v, hv⟩` from `hfu`.

Establish `: u = f - cycSub (Representation.ofMulAction ℤ G X) σ v` using `by rw [hv]; abel`. Rewrite using `[this, map_sub, AddMonoidHom.mem_ker.1 hf, normHom_cycSub, sub_zero]`. Establish `hsupp : ∀ y, u.coeff y ≠ 0 → orbitPoint G y = y`. Introduce `y hy`. Rewrite `hy` using `[hcoeff_u]`.

Take `⟨x, _, hx⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hy`. Establish `hxy : orbitPoint G x = y`. Assume the negation of the conclusion as `h`. Conclude with `hx (if_neg h)`. Rewrite using `[← hxy, orbitPoint_orbitPoint]`.

Establish `hu : u = 0`. Use extensionality with `p`. Rewrite using `[MonoidAlgebra.coeff_zero, Finsupp.zero_apply]`. Assume the negation of the conclusion as `hp`. Establish `hrep` using `hsupp p hp`.

Establish `h1` using `congrArg (fun f : MonoidAlgebra ℤ X => f.coeff p) hNu`. Simplify using `only [MonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h1`. Rewrite `h1` using `[coeff_normHom_ofMulAction]`. Rewrite `h1` using `[sum_smul_eq_of_support (fun y => u.coeff y) hsupp p, hrep]`. Establish `hs : (Nat.card (stabilizer G p) : ℤ) ≠ 0` using `by exact_mod_cast Nat.card_pos.ne'`.

Conclude with `hp ((mul_eq_zero.1 h1).resolve_left hs)`. Rewrite `hfu` using `[hu, sub_zero]`. Then use the resulting hypothesis.
-/
theorem ker_normHom_le_range_cycSub_ofMulAction (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    (normHom (Representation.ofMulAction ℤ G X)).ker ≤
      (cycSub (Representation.ofMulAction ℤ G X) σ).range := by
  classical
  have := Fintype.ofFinite X
  intro f hf
  let u : MonoidAlgebra ℤ X := ∑ x, f.coeff x • MonoidAlgebra.single (orbitPoint G x) 1
  have hcoeff_u : ∀ y, u.coeff y = ∑ x, if orbitPoint G x = y then f.coeff x else 0 := by
    intro y
    simp [u, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_apply]
  have hfu : f - u ∈ (cycSub (Representation.ofMulAction ℤ G X) σ).range := by
    have hf' : f - u = ∑ x, f.coeff x • (MonoidAlgebra.single x (1 : ℤ) -
        MonoidAlgebra.single (orbitPoint G x) 1) := by
      ext y
      rw [MonoidAlgebra.coeff_sub, Finsupp.sub_apply, hcoeff_u]
      simp [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single,
        Finsupp.single_apply, mul_sub, Finset.sum_sub_distrib]
    rw [hf']
    refine AddSubgroup.sum_mem _ fun x _ => AddSubgroup.zsmul_mem _ ?_ _
    obtain ⟨g, hg⟩ := orbitPoint_mem (G := G) x
    have : MonoidAlgebra.single (orbitPoint G x) (1 : ℤ) = (Representation.ofMulAction ℤ G X) g (MonoidAlgebra.single x 1) := by
      rw [Representation.ofMulAction_single, ← show g • x = orbitPoint G x from hg]
    rw [this, ← neg_sub]
    exact neg_mem (sub_mem_range_cycSub (Representation.ofMulAction ℤ G X) hσ g _)
  have hNu : normHom (Representation.ofMulAction ℤ G X) u = 0 := by
    obtain ⟨v, hv⟩ := hfu
    have : u = f - cycSub (Representation.ofMulAction ℤ G X) σ v := by rw [hv]; abel
    rw [this, map_sub, AddMonoidHom.mem_ker.1 hf, normHom_cycSub, sub_zero]
  have hsupp : ∀ y, u.coeff y ≠ 0 → orbitPoint G y = y := by
    intro y hy
    rw [hcoeff_u] at hy
    obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
    have hxy : orbitPoint G x = y := by
      by_contra h
      exact hx (if_neg h)
    rw [← hxy, orbitPoint_orbitPoint]
  have hu : u = 0 := by
    ext p
    rw [MonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    by_contra hp
    have hrep := hsupp p hp
    have h1 := congrArg (fun f : MonoidAlgebra ℤ X => f.coeff p) hNu
    simp only [MonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h1
    rw [coeff_normHom_ofMulAction] at h1
    rw [sum_smul_eq_of_support (fun y => u.coeff y) hsupp p, hrep] at h1
    have hs : (Nat.card (stabilizer G p) : ℤ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    exact hp ((mul_eq_zero.1 h1).resolve_left hs)
  rwa [hu, sub_zero] at hfu

/- English proof (translation)
Establish `: Subsingleton (KerModRange (normHom (Representation.ofMulAction ℤ G X)) (cycSub (Representation.ofMulAction ℤ G X) σ))`. Prove the components needed by the constructor for the conclusion. Introduce `a b`. Proceed by induction on `a using QuotientAddGroup.induction_on with | H a => ?_`. Proceed by induction on `b using QuotientAddGroup.induction_on with | H b => ?_`.

Rewrite using `[KerModRange.mk_eq_mk_iff]`. Conclude with `ker_normHom_le_range_cycSub_ofMulAction hσ (sub_mem a.2 b.2)`. Conclude with `Nat.card_of_subsingleton 0`.
-/
theorem natCard_kerModRange_normHom_ofMulAction (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (KerModRange (normHom (Representation.ofMulAction ℤ G X))
      (cycSub (Representation.ofMulAction ℤ G X) σ)) = 1 := by
  have : Subsingleton (KerModRange (normHom (Representation.ofMulAction ℤ G X))
      (cycSub (Representation.ofMulAction ℤ G X) σ)) := by
    constructor
    intro a b
    induction a using QuotientAddGroup.induction_on with | H a => ?_
    induction b using QuotientAddGroup.induction_on with | H b => ?_
    rw [KerModRange.mk_eq_mk_iff]
    exact ker_normHom_le_range_cycSub_ofMulAction hσ (sub_mem a.2 b.2)
  exact Nat.card_of_subsingleton 0

/- English proof (translation)
Use `set K := (cycSub (Representation.ofMulAction ℤ G X) σ).ker`. Set `s : orbitRel.Quotient G X → ℕ` to `fun ω => Nat.card (stabilizer G (Quotient.out ω))`. Establish `hs : ∀ ω, NeZero (s ω)` using `fun ω => ⟨Nat.card_pos.ne'⟩`. Set `Φ : K →+ ((ω : orbitRel.Quotient G X) → ZMod (s ω))` to `{ toFun := fun f ω => (((f : MonoidAlgebra ℤ X).coeff (Quotient.out ω) : ℤ) : ZMod (s ω)) map_zero' := by`. Use extensionality with `ω`.

Simplify using the standard rewrite rules. Use the proof step `map_add' := by`. Introduce `f f'`. Use extensionality with `ω`. Simplify using `}`.

Establish `hΦ : ∀ (f : K) ω, Φ f ω = (((f : MonoidAlgebra ℤ X).coeff (Quotient.out ω) : ℤ) : ZMod (s ω))` using `fun _ _ => rfl`. Establish `hsurj : Function.Surjective Φ`. Introduce `c`. Set `F : X → ℤ` to `fun x => ((c (Quotient.mk (orbitRel G X) x)).val : ℤ)`. Establish `hF : ∀ (g : G) x, F (g • x) = F x`.

Introduce `g x`. Simplify using `only [F]`. Rewrite using `[Quotient.sound (orbitRel_apply.2 (mem_orbit x g))]`. Use `⟨⟨permOfFun F, permOfFun_mem_ker hF⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `ω`.

Rewrite using `[hΦ, coeff_permOfFun]`. Establish `hω : Quotient.mk (orbitRel G X) (Quotient.out ω) = ω` using `Quotient.out_eq ω`. Establish `key : ∀ ω', ω' = ω → ((((c ω').val : ℕ) : ℤ) : ZMod (s ω)) = c ω`. Introduce and unpack `_ rfl`. Rewrite using `[Int.cast_natCast]`.

Conclude with `@ZMod.natCast_zmod_val _ (hs _) _`. Conclude with `key _ hω`. Establish `hker : Φ.ker = (normHom (Representation.ofMulAction ℤ G X)).range.addSubgroupOf K`. Use extensionality with `f`. Rewrite using `[AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]`.

Prove the components needed by the constructor for the conclusion. Introduce `hf`. Establish `hinv` using `coeff_smul_of_mem_ker hσ f.2`. Establish `hdiv : ∀ x, (Nat.card (stabilizer G x) : ℤ) ∣ (f : MonoidAlgebra ℤ X).coeff x`. Introduce `x`.

Establish `h1` using `congrFun hf (Quotient.mk (orbitRel G X) x)`. Rewrite `h1` using `[hΦ, Pi.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd]`. Take `⟨g, hg⟩` from `orbitPoint_mem (G := G) x`. Establish `h2 : Quotient.out (Quotient.mk (orbitRel G X) x) = g • x` using `hg.symm`. Rewrite `h1` using `[h2, hinv]`.

Simplify using `only [s, h2] at h1`. Rewrite `h1` using `[card_stabilizer_eq_of_mem (mem_orbit x g)]`. Then use the resulting hypothesis. Set `H : X → ℤ` to `fun y => if orbitPoint G y = y then (f : MonoidAlgebra ℤ X).coeff y / Nat.card (stabilizer G y) else 0`. Establish `hH : ∀ y, H y ≠ 0 → orbitPoint G y = y`. Introduce `y hy`.

Assume the negation of the conclusion as `h`. Conclude with `hy (if_neg h)`. Use `⟨permOfFun H, ?_⟩` and prove the remaining obligations. Use extensionality with `p`. Rewrite using `[coeff_normHom_ofMulAction]`.

Simplify using `only [coeff_permOfFun]`. Rewrite using `[sum_smul_eq_of_support H hH p]`. Simplify using `only [H, orbitPoint_orbitPoint, if_true]`. Take `⟨g, hg⟩` from `orbitPoint_mem (G := G) p`. Establish `hgp : g • p = orbitPoint G p` using `hg`.

Rewrite using `[card_stabilizer_eq_of_mem (orbitPoint_mem p), ← hgp, hinv, Int.mul_ediv_cancel' (hdiv p)]`. Introduce and unpack `⟨h, hh⟩`. Use function extensionality and compare the values at `ω`. Rewrite using `[hΦ, Pi.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd, ← hh, coeff_normHom_ofMulAction]`. Conclude with `card_stabilizer_dvd_sum _ _`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Nat.card_pi]`. Simplify using `only [Nat.card_zmod, s]`.
-/
theorem natCard_kerModRange_cycSub_ofMulAction [Fintype (orbitRel.Quotient G X)]
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (KerModRange (cycSub (Representation.ofMulAction ℤ G X) σ)
      (normHom (Representation.ofMulAction ℤ G X))) =
      ∏ ω : orbitRel.Quotient G X, Nat.card (stabilizer G (Quotient.out ω)) := by
  classical
  set K := (cycSub (Representation.ofMulAction ℤ G X) σ).ker
  let s : orbitRel.Quotient G X → ℕ := fun ω => Nat.card (stabilizer G (Quotient.out ω))
  have hs : ∀ ω, NeZero (s ω) := fun ω => ⟨Nat.card_pos.ne'⟩
  let Φ : K →+ ((ω : orbitRel.Quotient G X) → ZMod (s ω)) :=
    { toFun := fun f ω => (((f : MonoidAlgebra ℤ X).coeff (Quotient.out ω) : ℤ) : ZMod (s ω))
      map_zero' := by
        ext ω
        simp
      map_add' := by
        intro f f'
        ext ω
        simp }
  have hΦ : ∀ (f : K) ω, Φ f ω = (((f : MonoidAlgebra ℤ X).coeff (Quotient.out ω) : ℤ) :
      ZMod (s ω)) := fun _ _ => rfl
  have hsurj : Function.Surjective Φ := by
    intro c
    let F : X → ℤ := fun x => ((c (Quotient.mk (orbitRel G X) x)).val : ℤ)
    have hF : ∀ (g : G) x, F (g • x) = F x := by
      intro g x
      simp only [F]
      rw [Quotient.sound (orbitRel_apply.2 (mem_orbit x g))]
    refine ⟨⟨permOfFun F, permOfFun_mem_ker hF⟩, ?_⟩
    ext ω
    rw [hΦ, coeff_permOfFun]
    have hω : Quotient.mk (orbitRel G X) (Quotient.out ω) = ω := Quotient.out_eq ω
    have key : ∀ ω', ω' = ω → ((((c ω').val : ℕ) : ℤ) : ZMod (s ω)) = c ω := by
      rintro _ rfl
      rw [Int.cast_natCast]
      exact @ZMod.natCast_zmod_val _ (hs _) _
    exact key _ hω
  have hker : Φ.ker = (normHom (Representation.ofMulAction ℤ G X)).range.addSubgroupOf K := by
    ext f
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    constructor
    · intro hf
      have hinv := coeff_smul_of_mem_ker hσ f.2
      have hdiv : ∀ x, (Nat.card (stabilizer G x) : ℤ) ∣ (f : MonoidAlgebra ℤ X).coeff x := by
        intro x
        have h1 := congrFun hf (Quotient.mk (orbitRel G X) x)
        rw [hΦ, Pi.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
        obtain ⟨g, hg⟩ := orbitPoint_mem (G := G) x
        have h2 : Quotient.out (Quotient.mk (orbitRel G X) x) = g • x := hg.symm
        rw [h2, hinv] at h1
        simp only [s, h2] at h1
        rwa [card_stabilizer_eq_of_mem (mem_orbit x g)] at h1
      let H : X → ℤ := fun y =>
        if orbitPoint G y = y then (f : MonoidAlgebra ℤ X).coeff y / Nat.card (stabilizer G y)
        else 0
      have hH : ∀ y, H y ≠ 0 → orbitPoint G y = y := by
        intro y hy
        by_contra h
        exact hy (if_neg h)
      refine ⟨permOfFun H, ?_⟩
      ext p
      rw [coeff_normHom_ofMulAction]
      simp only [coeff_permOfFun]
      rw [sum_smul_eq_of_support H hH p]
      simp only [H, orbitPoint_orbitPoint, if_true]
      obtain ⟨g, hg⟩ := orbitPoint_mem (G := G) p
      have hgp : g • p = orbitPoint G p := hg
      rw [card_stabilizer_eq_of_mem (orbitPoint_mem p), ← hgp, hinv, Int.mul_ediv_cancel' (hdiv p)]
    · rintro ⟨h, hh⟩
      funext ω
      rw [hΦ, Pi.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd, ← hh, coeff_normHom_ofMulAction]
      exact card_stabilizer_dvd_sum _ _
  calc Nat.card (KerModRange (cycSub (Representation.ofMulAction ℤ G X) σ) (normHom (Representation.ofMulAction ℤ G X)))
      = Nat.card (K ⧸ Φ.ker) :=
        Nat.card_congr (QuotientAddGroup.quotientAddEquivOfEq hker.symm).toEquiv
    _ = Nat.card ((ω : orbitRel.Quotient G X) → ZMod (s ω)) :=
        Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective Φ hsurj).toEquiv
    _ = ∏ ω : orbitRel.Quotient G X, Nat.card (stabilizer G (Quotient.out ω)) := by
        rw [Nat.card_pi]
        simp only [Nat.card_zmod, s]

/- English proof (translation)
Rewrite using `[cyclicHerbrand, herbrandQuotient, natCard_kerModRange_cycSub_ofMulAction hσ, natCard_kerModRange_normHom_ofMulAction hσ, Nat.cast_one, div_one, Nat.cast_prod]`.
-/
theorem cyclicHerbrand_ofMulAction [Fintype (orbitRel.Quotient G X)]
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cyclicHerbrand (Representation.ofMulAction ℤ G X) σ =
      ∏ ω : orbitRel.Quotient G X, (Nat.card (stabilizer G (Quotient.out ω)) : ℚ) := by
  rw [cyclicHerbrand, herbrandQuotient, natCard_kerModRange_cycSub_ofMulAction hσ,
    natCard_kerModRange_normHom_ofMulAction hσ, Nat.cast_one, div_one, Nat.cast_prod]

end Cohomology

section Quotient

variable {G : Type*} [Group G] [Fintype G]

end Quotient

end GroundTheory.Global
