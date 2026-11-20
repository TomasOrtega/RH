import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenRoots

open ReciprocityTheory.Gal UpperTheory.V.Base

/- English proof (translation)
Establish `h1 : (f.restrict hP) ^ n = 1`. Use extensionality with `x`. Rewrite using `[Module.End.pow_restrict]`. Simplify using `[hf]`. Use `(lenRoots O P n ζ hn hζ (f.restrict hP) h1).1.trans ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_range]`. Use `Finset.sum_le_sum fun j _ => ?_` and prove the remaining obligations. Use `Module.length_le_of_injective (LinearMap.codRestrict _ (P.subtype ∘ₗ Submodule.subtype _) fun x => ⟨x.1.2, ?_⟩) ?_` and prove the remaining obligations. Use `congrArg Subtype.val (LinearMap.mem_ker.1 x.2)` as an intermediate fact. Conclude with `this`.

Introduce `x y h`. Use `congrArg Subtype.val h` as an intermediate fact. Conclude with `Subtype.ext (Subtype.ext this)`.
-/
private theorem lenEigLe_one {O N : Type} [CommRing O] [IsDomain O] [AddCommGroup N] [Module O N]
    (n : ℕ) (ζ : O) (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (f : Module.End O N) (hf : f ^ n = 1)
    (P : Submodule O N) (hP : ∀ x ∈ P, f x ∈ P) :
    Module.length O P ≤ ∑ j : Fin n,
      Module.length O (P ⊓ LinearMap.ker (f - ζ ^ (j : ℕ) • (1 : Module.End O N)) : Submodule O N) := by
  have h1 : (f.restrict hP) ^ n = 1 := by
    ext x
    rw [Module.End.pow_restrict]
    simp [hf]
  refine (lenRoots O P n ζ hn hζ (f.restrict hP) h1).1.trans ?_
  rw [Finset.sum_range]
  refine Finset.sum_le_sum fun j _ => ?_
  refine Module.length_le_of_injective
    (LinearMap.codRestrict _ (P.subtype ∘ₗ Submodule.subtype _) fun x => ⟨x.1.2, ?_⟩) ?_
  · have := congrArg Subtype.val (LinearMap.mem_ker.1 x.2)
    exact this
  · intro x y h
    have := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext this)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `n ζ _ _ f _ _ P _`. Rewrite using `[Fintype.sum_unique, iInf_of_empty, inf_top_eq]`. Consider the case `succ k ih`.

Introduce `n ζ hn hζ f hf hc P hP`. Use `(lenEigLe_one (n 0) (ζ 0) (hn 0) (hζ 0) (f 0) (hf 0) P (hP 0)).trans ?_` and prove the remaining obligations. Rewrite using `[← (Fin.consEquiv fun i => Fin (n i)).sum_comp, Fintype.sum_prod_type]`. Use `Finset.sum_le_sum fun j _ => ?_` and prove the remaining obligations. Use `(ih (fun i => n i.succ) (fun i => ζ i.succ) (fun i => hn _) (fun i => hζ _) (fun i => f i.succ) (fun i => hf _) (fun i j => hc _ _) _ ?_).trans (le_of_eq ?_)` and prove the remaining obligations.

Introduce `i x hx`. Use `⟨hP _ x hx.1, ?_⟩` and prove the remaining obligations. Establish `h2 : f 0 x = ζ 0 ^ (j : ℕ) • x` using `by simpa [sub_eq_zero] using hx.2`. Establish `h3 : f 0 (f i.succ x) = ζ 0 ^ (j : ℕ) • f i.succ x`. Rewrite using `[← Module.End.mul_apply, hc, Module.End.mul_apply, h2, map_smul]`.

Simplify `h3` using `[sub_eq_zero]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Establish `: (P ⊓ LinearMap.ker (f 0 - ζ 0 ^ (j : ℕ) • (1 : Module.End O N))) ⊓ ⨅ i : Fin k, LinearMap.ker (f i.succ - ζ i.succ ^ (a i : ℕ) • (1 : Module.End O N)) = P ⊓ ⨅ i, LinearMap.ker (f i - ζ i ^ (((Fin.consEquiv fun i => Fin (n i)) (j, a) i : Fin (n i)) : ℕ) • (1 : Module.End O N))`. Use extensionality with `x`. Simplify using `only [Submodule.mem_inf, Submodule.mem_iInf, Fin.forall_fin_succ, and_assoc]`.

Both sides reduce to the same expression. Rewrite using `[this]`.
-/
private theorem lenEigLe_many {O N : Type} [CommRing O] [IsDomain O] [AddCommGroup N] [Module O N] (k : ℕ) :
    ∀ (n : Fin k → ℕ) (ζ : Fin k → O), (∀ i, 0 < n i) → (∀ i, IsPrimitiveRoot (ζ i) (n i)) →
      ∀ f : Fin k → Module.End O N, (∀ i, f i ^ n i = 1) → (∀ i j, f i * f j = f j * f i) →
      ∀ P : Submodule O N, (∀ i, ∀ x ∈ P, f i x ∈ P) →
      Module.length O P ≤ ∑ a : (∀ i, Fin (n i)),
        Module.length O (P ⊓ ⨅ i, LinearMap.ker (f i - ζ i ^ (a i : ℕ) • (1 : Module.End O N)) : Submodule O N) := by
  induction k with
  | zero =>
    intro n ζ _ _ f _ _ P _
    rw [Fintype.sum_unique, iInf_of_empty, inf_top_eq]
  | succ k ih =>
    intro n ζ hn hζ f hf hc P hP
    refine (lenEigLe_one (n 0) (ζ 0) (hn 0) (hζ 0) (f 0) (hf 0) P (hP 0)).trans ?_
    rw [← (Fin.consEquiv fun i => Fin (n i)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun j _ => ?_
    refine (ih (fun i => n i.succ) (fun i => ζ i.succ) (fun i => hn _) (fun i => hζ _) (fun i => f i.succ)
      (fun i => hf _) (fun i j => hc _ _) _ ?_).trans (le_of_eq ?_)
    · intro i x hx
      refine ⟨hP _ x hx.1, ?_⟩
      have h2 : f 0 x = ζ 0 ^ (j : ℕ) • x := by simpa [sub_eq_zero] using hx.2
      have h3 : f 0 (f i.succ x) = ζ 0 ^ (j : ℕ) • f i.succ x := by
        rw [← Module.End.mul_apply, hc, Module.End.mul_apply, h2, map_smul]
      simpa [sub_eq_zero] using h3
    · refine Finset.sum_congr rfl fun a _ => ?_
      have : (P ⊓ LinearMap.ker (f 0 - ζ 0 ^ (j : ℕ) • (1 : Module.End O N))) ⊓
          ⨅ i : Fin k, LinearMap.ker (f i.succ - ζ i.succ ^ (a i : ℕ) • (1 : Module.End O N)) =
          P ⊓ ⨅ i, LinearMap.ker (f i - ζ i ^
            (((Fin.consEquiv fun i => Fin (n i)) (j, a) i : Fin (n i)) : ℕ) • (1 : Module.End O N)) := by
        ext x
        simp only [Submodule.mem_inf, Submodule.mem_iInf, Fin.forall_fin_succ, and_assoc]
        rfl
      rw [this]

/- English proof (translation)
Take `⟨ι, _, n, hn, ⟨e⟩⟩` from `CommGroup.equiv_prod_multiplicative_zmod_of_finite Q`. Set `σ` to `(Fintype.equivFin ι).symm`. Use `haveI : ∀ i, NeZero (n i) := fun i => ⟨by have := hn i; omega⟩`. Use `⟨_, fun i => n (σ i), fun i => e.symm (Pi.mulSingle (σ i) (Multiplicative.ofAdd 1)), fun i => zero_lt_one.trans (hn (σ i)), fun i => ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[MulEquiv.orderOf_eq]`.

Use `orderOf_injective (MonoidHom.mulSingle (fun i => Multiplicative (ZMod (n i))) (σ i)) (Pi.mulSingle_injective (M := fun i => Multiplicative (ZMod (n i))) (σ i)) (Multiplicative.ofAdd 1)` as an intermediate fact. Rewrite `this` using `[MonoidHom.mulSingle_apply]`. Rewrite using `[this, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]`. Rewrite using `[eq_top_iff]`. Introduce `q _`.

Take `⟨y, rfl⟩` from `e.symm.surjective q`. Rewrite using `[← Finset.univ_prod_mulSingle y, map_prod]`. Use `Submonoid.prod_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨i, rfl⟩` from `σ.surjective i`. Establish `: y (σ i) = Multiplicative.ofAdd (1 : ZMod (n (σ i))) ^ (y (σ i)).toAdd.val`.

Rewrite using `[← ofAdd_nsmul]`. Simplify using the standard rewrite rules. Rewrite using `[this, Pi.mulSingle_pow, map_pow]`. Conclude with `Submonoid.pow_mem _ (Submonoid.subset_closure (Set.mem_range_self i)) _`. Introduce `C _ u hu`.

Establish `hu' : ∀ i, u (σ.symm i) ^ n i = 1` using `fun i => by simpa using hu (σ.symm i)`. Use `⟨(∏ i, (AddChar.zmodChar (n i) (hu' i)).toMonoidHom.comp (Pi.evalMonoidHom (fun i => Multiplicative (ZMod (n i))) i)).comp e.toMonoidHom, fun i => ?_⟩` and prove the remaining obligations. Simplify using `only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, MonoidHom.finset_prod_apply, Pi.evalMonoidHom_apply]`. Rewrite using `[Finset.prod_eq_single (σ i)]`. Use `haveI : Fact (1 < n (σ i)) := ⟨hn _⟩`.

Simplify using `[AddChar.zmodChar_apply, ZMod.val_one]`. Introduce `j _ hj`. Rewrite using `[Pi.mulSingle_eq_of_ne hj, map_one]`. Simplify using the standard rewrite rules.
-/
private theorem lenEigLe_gen (Q : Type) [CommGroup Q] [Finite Q] :
    ∃ (k : ℕ) (n : Fin k → ℕ) (g : Fin k → Q), (∀ i, 0 < n i) ∧ (∀ i, orderOf (g i) = n i) ∧
      Submonoid.closure (Set.range g) = ⊤ ∧
      ∀ (C : Type) [CommGroup C] (u : Fin k → C), (∀ i, u i ^ n i = 1) → ∃ ψ : Q →* C, ∀ i, ψ (g i) = u i := by
  classical
  obtain ⟨ι, _, n, hn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite Q
  let σ := (Fintype.equivFin ι).symm
  haveI : ∀ i, NeZero (n i) := fun i => ⟨by have := hn i; omega⟩
  refine ⟨_, fun i => n (σ i), fun i => e.symm (Pi.mulSingle (σ i) (Multiplicative.ofAdd 1)),
    fun i => zero_lt_one.trans (hn (σ i)), fun i => ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    have := orderOf_injective (MonoidHom.mulSingle (fun i => Multiplicative (ZMod (n i))) (σ i))
      (Pi.mulSingle_injective (M := fun i => Multiplicative (ZMod (n i))) (σ i)) (Multiplicative.ofAdd 1)
    rw [MonoidHom.mulSingle_apply] at this
    rw [this, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  · rw [eq_top_iff]
    intro q _
    obtain ⟨y, rfl⟩ := e.symm.surjective q
    rw [← Finset.univ_prod_mulSingle y, map_prod]
    refine Submonoid.prod_mem _ fun i _ => ?_
    obtain ⟨i, rfl⟩ := σ.surjective i
    have : y (σ i) = Multiplicative.ofAdd (1 : ZMod (n (σ i))) ^ (y (σ i)).toAdd.val := by
      rw [← ofAdd_nsmul]; simp
    rw [this, Pi.mulSingle_pow, map_pow]
    exact Submonoid.pow_mem _ (Submonoid.subset_closure (Set.mem_range_self i)) _
  · intro C _ u hu
    have hu' : ∀ i, u (σ.symm i) ^ n i = 1 := fun i => by simpa using hu (σ.symm i)
    refine ⟨(∏ i, (AddChar.zmodChar (n i) (hu' i)).toMonoidHom.comp
      (Pi.evalMonoidHom (fun i => Multiplicative (ZMod (n i))) i)).comp e.toMonoidHom, fun i => ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
      MonoidHom.finset_prod_apply, Pi.evalMonoidHom_apply]
    rw [Finset.prod_eq_single (σ i)]
    · haveI : Fact (1 < n (σ i)) := ⟨hn _⟩
      simp [AddChar.zmodChar_apply, ZMod.val_one]
    · intro j _ hj
      rw [Pi.mulSingle_eq_of_ne hj, map_one]
    · simp

/- English proof (translation)
Introduce `O Q N _ _ _ _ _ _ _ _ π`. Take `⟨k, n, g, hn, hg, hcl, hψ⟩` from `lenEigLe_gen Q`. Establish `hζ : ∀ i, ∃ ζ : Oˣ, IsPrimitiveRoot ζ (n i)` using `fun i => by`. Take `⟨z, hz⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot O (Monoid.exponent Q)`. Establish `he : 0 < Monoid.exponent Q` using `Nat.pos_of_ne_zero Monoid.exponent_ne_zero_of_finite`.

Take `⟨m, hm⟩ : n i ∣ Monoid.exponent Q` from `hg i ▸ Monoid.order_dvd_exponent (g i)`. Establish `h` using `hz.pow he (hm.trans (mul_comm _ _))`. Conclude with `⟨_, h.isUnit_unit (hn i).ne'⟩`. Use `choose ζ hζ using hζ`. Establish `h1` using `lenEigLe_many k n (fun i => (ζ i : O)) hn (fun i => IsPrimitiveRoot.coe_units_iff.2 (hζ i)) (fun i => π (g i)) (fun i => by rw [← map_pow, ← hg i, pow_orderOf_eq_one, map_one]) (fun i j => by rw [← map_mul, mul_comm, map_mul]) ⊤ (fun _ _ _ => trivial)`.

Establish `h2 : ∀ a : (∀ i, Fin (n i)), ∃ ψ : Q →* Oˣ, ∀ i, ψ (g i) = ζ i ^ (a i : ℕ)` using `fun a => hψ Oˣ _ fun i => by rw [← pow_mul, mul_comm, pow_mul, (hζ i).pow_eq_one, one_pow]`. Use `choose ψ hψ' using h2`. Establish `hinj : Function.Injective ψ` using `fun a b h => funext fun i => Fin.ext <| (hζ i).pow_inj (a i).2 (b i).2 (by rw [← hψ', ← hψ', h])`. Rewrite `h1` using `[Module.length_top]`. Use `h1.trans ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Use `Module.length_le_of_injective (Submodule.inclusion ?_) (Submodule.inclusion_injective _)` and prove the remaining obligations. Introduce `x hx`. Rewrite using `[mem_eig]`. Introduce `q`.

Establish `hq : q ∈ Submonoid.closure (Set.range g)` using `hcl ▸ Submonoid.mem_top q`. Proceed by induction on `hq using Submonoid.closure_induction with`. Consider the case `mem q hq`. Take `⟨i, rfl⟩` from `hq`. Use `(Submodule.mem_iInf _).1 hx.2 i` as an intermediate fact.

Rewrite using `[hψ']`. Simplify `this` using `[sub_eq_zero]`. Consider the case `one => simp`. Consider the case `mul p q _ _ hp hq`. Rewrite using `[map_mul, Module.End.mul_apply, hq, map_smul, hp, map_mul, Units.val_mul, smul_smul, mul_comm]`.
-/
theorem UpperTheory.V.Base.lenEigLe :
    ∀ (O Q N : Type) [CommRing O] [IsDomain O] [CommGroup Q] [Finite Q] [HasEnoughRootsOfUnity O (Monoid.exponent Q)]
      [Fintype (Q →* Oˣ)] [AddCommGroup N] [Module O N] (π : Representation O Q N),
      Module.length O N ≤ ∑ ψ : Q →* Oˣ, Module.length O (eig π ψ) := by
  intro O Q N _ _ _ _ _ _ _ _ π
  classical
  obtain ⟨k, n, g, hn, hg, hcl, hψ⟩ := lenEigLe_gen Q
  have hζ : ∀ i, ∃ ζ : Oˣ, IsPrimitiveRoot ζ (n i) := fun i => by
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot O (Monoid.exponent Q)
    have he : 0 < Monoid.exponent Q := Nat.pos_of_ne_zero Monoid.exponent_ne_zero_of_finite
    obtain ⟨m, hm⟩ : n i ∣ Monoid.exponent Q := hg i ▸ Monoid.order_dvd_exponent (g i)
    have h := hz.pow he (hm.trans (mul_comm _ _))
    exact ⟨_, h.isUnit_unit (hn i).ne'⟩
  choose ζ hζ using hζ
  have h1 := lenEigLe_many k n (fun i => (ζ i : O)) hn (fun i => IsPrimitiveRoot.coe_units_iff.2 (hζ i))
    (fun i => π (g i)) (fun i => by rw [← map_pow, ← hg i, pow_orderOf_eq_one, map_one])
    (fun i j => by rw [← map_mul, mul_comm, map_mul]) ⊤ (fun _ _ _ => trivial)
  have h2 : ∀ a : (∀ i, Fin (n i)), ∃ ψ : Q →* Oˣ, ∀ i, ψ (g i) = ζ i ^ (a i : ℕ) := fun a =>
    hψ Oˣ _ fun i => by rw [← pow_mul, mul_comm, pow_mul, (hζ i).pow_eq_one, one_pow]
  choose ψ hψ' using h2
  have hinj : Function.Injective ψ := fun a b h => funext fun i => Fin.ext <|
    (hζ i).pow_inj (a i).2 (b i).2 (by rw [← hψ', ← hψ', h])
  rw [Module.length_top] at h1
  refine h1.trans ?_
  calc _ ≤ ∑ a, Module.length O (eig π (ψ a)) := Finset.sum_le_sum fun a _ => ?_
    _ = ∑ χ ∈ Finset.univ.image ψ, Module.length O (eig π χ) :=
      (Finset.sum_image (f := fun χ => Module.length O (eig π χ)) fun a _ b _ h => hinj h).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  refine Module.length_le_of_injective (Submodule.inclusion ?_) (Submodule.inclusion_injective _)
  intro x hx
  rw [mem_eig]
  intro q
  have hq : q ∈ Submonoid.closure (Set.range g) := hcl ▸ Submonoid.mem_top q
  induction hq using Submonoid.closure_induction with
  | mem q hq =>
    obtain ⟨i, rfl⟩ := hq
    have := (Submodule.mem_iInf _).1 hx.2 i
    rw [hψ']
    simpa [sub_eq_zero] using this
  | one => simp
  | mul p q _ _ hp hq =>
    rw [map_mul, Module.End.mul_apply, hq, map_smul, hp, map_mul, Units.val_mul, smul_smul, mul_comm]
