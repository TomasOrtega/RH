import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

/- English proof (translation)
Use `letI := ZMod.algebra k l`. Use `haveI : Module.Finite (ZMod l) k := Module.Finite.of_finite`. Set `N : Subgroup G` to `χ.ker ⊓ ψ.ker`. Establish `hNo : IsOpen (N : Set G)` using `by show IsOpen ((χ.ker ⊓ ψ.ker : Subgroup G) : Set G)`. Rewrite using `[Subgroup.coe_inf]`.

Conclude with `hχ.inter hψ`. Use `haveI : Finite (G ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNo`. Use `haveI := hΦ N hNo`. Set `b` to `Module.finBasis (ZMod l) k`. Establish `mem : ∀ a ∈ Z1 χ ψ, IsLocallyConstant a ∧ ∀ g h : G, a (g * h) = (χ g : k) * a h + a g * (ψ h : k)` using `fun a ha => ha`.

Establish `hadd : ∀ a ∈ Z1 χ ψ, ∀ x y : N, a ((x : G) * (y : G)) = a x + a y`. Introduce `a ha x y`. Establish `hx : χ (x : G) = 1` using `MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp x.2).1`. Establish `hy : ψ (y : G) = 1` using `MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp y.2).2`. Rewrite using `[(mem a ha).2, hx, hy]`.

Simplify using `[add_comm]`. Set `φ : ∀ a ∈ Z1 χ ψ, Fin (Module.finrank (ZMod l) k) → (N →* Multiplicative (ZMod l))` to `fun a ha i => MonoidHom.mk' (fun x => Multiplicative.ofAdd (b.repr (a x) i)) (by`. Introduce `x y`. Simplify using `[hadd a ha x y, ofAdd_add])`. Establish `hφo : ∀ a (ha : a ∈ Z1 χ ψ) i, IsOpen ((φ a ha i).ker : Set N)`.

Introduce `a ha i`. Establish `hlc : IsLocallyConstant (fun x : N => b.repr (a x) i)` using `((mem a ha).1.comp_continuous continuous_subtype_val).comp (fun y => b.repr y i)`. Establish `e : ((φ a ha i).ker : Set N) = {x | (fun x : N => b.repr (a x) i) x = 0}`. Use extensionality with `x`. Simplify using `[φ, MonoidHom.mem_ker]`.

Rewrite using `[e]`. Conclude with `hlc.isOpen_fiber 0`. Set `F : Z1 χ ψ → (G ⧸ N → k) × (Fin (Module.finrank (ZMod l) k) → {φ : N →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set N)})` to `fun a => (fun q => (a : G → k) q.out, fun i => ⟨φ a a.2 i, hφo a a.2 i⟩)`. Use `Finite.of_injective F ?_` and prove the remaining obligations. Introduce and unpack `⟨a, ha⟩ ⟨a', ha'⟩ h`.

Simplify using `only [F, Prod.mk.injEq] at h`. Take `⟨h1, h2⟩` from `h`. Establish `hN' : ∀ x : N, a x = a' x`. Introduce `x`. Apply `b.repr.injective` to reduce the goal to its premises.

Use extensionality with `i`. Conclude with `congrArg (fun f => Multiplicative.toAdd ((f i).1 x)) h2`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Take `⟨n, hn⟩` from `QuotientGroup.mk_out_eq_mul N g`.

Establish `e1 : a (QuotientGroup.mk g : G ⧸ N).out = a' (QuotientGroup.mk g : G ⧸ N).out` using `congrFun h1 _`. Establish `hg : g = (QuotientGroup.mk g : G ⧸ N).out * ((n⁻¹ : N) : G)`. Rewrite using `[hn]`. Simplify using `[mul_assoc]`. Use `show a g = a' g`.

Rewrite using `[hg, (mem a ha).2, (mem a' ha').2, hN' n⁻¹, e1]`.
-/
private theorem module_finite_z1_padicInt (l : ℕ) [Fact l.Prime] {k G : Type} [Field k] [Finite k] [CharP k l] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (χ ψ : G →* kˣ) (hΦ : PhiCond G l)
    (hχ : IsOpen (χ.ker : Set G)) (hψ : IsOpen (ψ.ker : Set G)) : Finite (Z1 χ ψ) := by
  classical
  letI := ZMod.algebra k l
  haveI : Module.Finite (ZMod l) k := Module.Finite.of_finite
  let N : Subgroup G := χ.ker ⊓ ψ.ker
  have hNo : IsOpen (N : Set G) := by
    show IsOpen ((χ.ker ⊓ ψ.ker : Subgroup G) : Set G)
    rw [Subgroup.coe_inf]
    exact hχ.inter hψ
  haveI : Finite (G ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNo
  haveI := hΦ N hNo
  let b := Module.finBasis (ZMod l) k
  have mem : ∀ a ∈ Z1 χ ψ, IsLocallyConstant a ∧
      ∀ g h : G, a (g * h) = (χ g : k) * a h + a g * (ψ h : k) := fun a ha => ha
  have hadd : ∀ a ∈ Z1 χ ψ, ∀ x y : N, a ((x : G) * (y : G)) = a x + a y := by
    intro a ha x y
    have hx : χ (x : G) = 1 := MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp x.2).1
    have hy : ψ (y : G) = 1 := MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp y.2).2
    rw [(mem a ha).2, hx, hy]
    simp [add_comm]
  let φ : ∀ a ∈ Z1 χ ψ, Fin (Module.finrank (ZMod l) k) → (N →* Multiplicative (ZMod l)) :=
    fun a ha i => MonoidHom.mk' (fun x => Multiplicative.ofAdd (b.repr (a x) i)) (by
      intro x y
      simp [hadd a ha x y, ofAdd_add])
  have hφo : ∀ a (ha : a ∈ Z1 χ ψ) i, IsOpen ((φ a ha i).ker : Set N) := by
    intro a ha i
    have hlc : IsLocallyConstant (fun x : N => b.repr (a x) i) :=
      ((mem a ha).1.comp_continuous continuous_subtype_val).comp (fun y => b.repr y i)
    have e : ((φ a ha i).ker : Set N) = {x | (fun x : N => b.repr (a x) i) x = 0} := by
      ext x
      simp [φ, MonoidHom.mem_ker]
    rw [e]
    exact hlc.isOpen_fiber 0
  let F : Z1 χ ψ → (G ⧸ N → k) ×
      (Fin (Module.finrank (ZMod l) k) → {φ : N →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set N)}) :=
    fun a => (fun q => (a : G → k) q.out, fun i => ⟨φ a a.2 i, hφo a a.2 i⟩)
  refine Finite.of_injective F ?_
  rintro ⟨a, ha⟩ ⟨a', ha'⟩ h
  simp only [F, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hN' : ∀ x : N, a x = a' x := by
    intro x
    apply b.repr.injective
    ext i
    exact congrArg (fun f => Multiplicative.toAdd ((f i).1 x)) h2
  apply Subtype.ext
  funext g
  obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N g
  have e1 : a (QuotientGroup.mk g : G ⧸ N).out = a' (QuotientGroup.mk g : G ⧸ N).out := congrFun h1 _
  have hg : g = (QuotientGroup.mk g : G ⧸ N).out * ((n⁻¹ : N) : G) := by
    rw [hn]; simp [mul_assoc]
  show a g = a' g
  rw [hg, (mem a ha).2, (mem a' ha').2, hN' n⁻¹, e1]

/- English proof (translation)
Introduce `l _ n k G _ _ _ _ _ _ _ _ χ hΦ hopen hinj`. Use `⟨∑ i, ∑ j, Module.finrank k (Z1 (χ i) (χ j)), hopen, hinj, fun i j _ => ?_⟩` and prove the remaining obligations. Use `haveI := module_finite_z1_padicInt l (χ i) (χ j) hΦ (hopen i) (hopen j)`. Use `⟨inferInstance, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.V.CA.exists_multFree_of_phiCond_of_injective_chars :
    ∀ (l : ℕ) [Fact l.Prime] {n : ℕ} {k G : Type} [Field k] [Finite k] [CharP k l] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (χ : Fin n → G →* kˣ), PhiCond G l → (∀ i, IsOpen ((χ i).ker : Set G)) → Function.Injective χ → ∃ h, MultFree χ h := by
  intro l _ n k G _ _ _ _ _ _ _ _ χ hΦ hopen hinj
  refine ⟨∑ i, ∑ j, Module.finrank k (Z1 (χ i) (χ j)), hopen, hinj, fun i j _ => ?_⟩
  haveI := module_finite_z1_padicInt l (χ i) (χ j) hΦ (hopen i) (hopen j)
  refine ⟨inferInstance, ?_⟩
  calc Module.finrank k (Z1 (χ i) (χ j)) ≤ ∑ j', Module.finrank k (Z1 (χ i) (χ j')) :=
        Finset.single_le_sum (f := fun j' => Module.finrank k (Z1 (χ i) (χ j')))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', Module.finrank k (Z1 (χ i') (χ j')) :=
        Finset.single_le_sum (f := fun i' => ∑ j', Module.finrank k (Z1 (χ i') (χ j')))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
