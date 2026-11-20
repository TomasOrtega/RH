import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BoxDefs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

/- English proof (translation)
Use `haveI : TotallySeparatedSpace (G ⧸ N) := by`. Rewrite using `[totallySeparatedSpace_iff_exists_isClopen]`. Introduce `a b hab`. Take `⟨x, rfl⟩` from `QuotientGroup.mk_surjective a`. Take `⟨y, rfl⟩` from `QuotientGroup.mk_surjective b`.

Establish `hxy : x⁻¹ * y ∉ ((ClosedSubgroup.mk N hN : ClosedSubgroup G) : Subgroup G)` using `fun h => hab (QuotientGroup.eq.2 h)`. Rewrite `hxy` using `[ProfiniteGrp.closedSubgroup_eq_sInf_open (ClosedSubgroup.mk N hN), Subgroup.mem_sInf]`. Use `push_neg at hxy`. Take `⟨U, ⟨hUo, hNU⟩, hyU⟩` from `hxy`. Set `W : Set G` to `{g | x⁻¹ * g ∈ U}`.

Establish `hWo : IsOpen W` using `by show IsOpen ((fun g => x⁻¹ * g) ⁻¹' (U : Set G))`. Conclude with `hUo.preimage (continuous_const.mul continuous_id)`. Establish `hWc : IsClosed W` using `by show IsClosed ((fun g => x⁻¹ * g) ⁻¹' (U : Set G))`. Conclude with `(Subgroup.isClosed_of_isOpen U hUo).preimage (continuous_const.mul continuous_id)`. Establish `hsat : (QuotientGroup.mk : G → G ⧸ N) ⁻¹' (QuotientGroup.mk '' W) = W`.

Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, hh, he⟩`. Establish `hn` using `QuotientGroup.eq.1 he`. Use `show x⁻¹ * g ∈ U`.

Use `U.mul_mem hh (hNU hn)` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Introduce `hg`. Conclude with `⟨g, hg, rfl⟩`. Use `⟨QuotientGroup.mk '' W, ⟨?_, QuotientGroup.isOpenMap_coe W hWo⟩, ⟨x, by simp [W], rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[← (QuotientGroup.isQuotientMap_mk N).isCoinducing.isClosed_preimage, hsat]`. Conclude with `hWc`. Introduce `hy`. Establish `hy' : y ∈ (QuotientGroup.mk : G → G ⧸ N) ⁻¹' (QuotientGroup.mk '' W)` using `hy`. Rewrite `hy'` using `[hsat]`.

Conclude with `hyU hy'`. Use `infer_instance`.
-/
private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  haveI : TotallySeparatedSpace (G ⧸ N) := by
    rw [totallySeparatedSpace_iff_exists_isClopen]
    intro a b hab
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    have hxy : x⁻¹ * y ∉ ((ClosedSubgroup.mk N hN : ClosedSubgroup G) : Subgroup G) :=
      fun h => hab (QuotientGroup.eq.2 h)
    rw [ProfiniteGrp.closedSubgroup_eq_sInf_open (ClosedSubgroup.mk N hN), Subgroup.mem_sInf] at hxy
    push_neg at hxy
    obtain ⟨U, ⟨hUo, hNU⟩, hyU⟩ := hxy
    let W : Set G := {g | x⁻¹ * g ∈ U}
    have hWo : IsOpen W := by
      show IsOpen ((fun g => x⁻¹ * g) ⁻¹' (U : Set G))
      exact hUo.preimage (continuous_const.mul continuous_id)
    have hWc : IsClosed W := by
      show IsClosed ((fun g => x⁻¹ * g) ⁻¹' (U : Set G))
      exact (Subgroup.isClosed_of_isOpen U hUo).preimage (continuous_const.mul continuous_id)
    have hsat : (QuotientGroup.mk : G → G ⧸ N) ⁻¹' (QuotientGroup.mk '' W) = W := by
      ext g
      constructor
      · rintro ⟨h, hh, he⟩
        have hn := QuotientGroup.eq.1 he
        show x⁻¹ * g ∈ U
        have := U.mul_mem hh (hNU hn)
        simpa [mul_assoc] using this
      · intro hg
        exact ⟨g, hg, rfl⟩
    refine ⟨QuotientGroup.mk '' W, ⟨?_, QuotientGroup.isOpenMap_coe W hWo⟩, ⟨x, by simp [W], rfl⟩, ?_⟩
    · rw [← (QuotientGroup.isQuotientMap_mk N).isCoinducing.isClosed_preimage, hsat]
      exact hWc
    · intro hy
      have hy' : y ∈ (QuotientGroup.mk : G → G ⧸ N) ⁻¹' (QuotientGroup.mk '' W) := hy
      rw [hsat] at hy'
      exact hyU hy'
  infer_instance

private def permR (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) :
    Representation R Γ (Γ ⧸ H → R) where
  toFun g := LinearMap.funLeft R R fun x => g⁻¹ • x
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_smul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem permR_apply (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (f : Γ ⧸ H → R)
    (x : Γ ⧸ H) : permR R H g f x = f (g⁻¹ • x) := rfl

/- English proof (translation)
Establish `h1 : ((g⁻¹ * x.out : Γ) : Γ ⧸ H) = (((g⁻¹ • x).out : Γ) : Γ ⧸ H)`. Rewrite using `[QuotientGroup.out_eq']`. Use `conv_rhs => rw [← QuotientGroup.out_eq' x]`. Both sides reduce to the same expression. Establish `h2` using `QuotientGroup.eq.1 h1`.

Simplify `h2` using `[mul_assoc]`.
-/
private theorem sec_mem {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (x : Γ ⧸ H) :
    (x.out)⁻¹ * g * (g⁻¹ • x).out ∈ H := by
  have h1 : ((g⁻¹ * x.out : Γ) : Γ ⧸ H) = (((g⁻¹ • x).out : Γ) : Γ ⧸ H) := by
    rw [QuotientGroup.out_eq']
    conv_rhs => rw [← QuotientGroup.out_eq' x]
    rfl
  have h2 := QuotientGroup.eq.1 h1
  simpa [mul_assoc] using h2

/- English proof (translation)
Introduce `H hH`. Use `haveI : Finite (Γ ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH`. Establish `getN : ∀ W : Set Γ, IsClopen W → (1 : Γ) ∈ W → ∃ N : Subgroup Γ, N.Normal ∧ IsOpen (N : Set Γ) ∧ (N : Set Γ) ⊆ W`. Introduce `W hW h1`. Take `⟨N, hN⟩` from `IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one hW h1`.

Conclude with `⟨N.toOpenSubgroup, N.isNormal', N.toOpenSubgroup.isOpen, hN⟩`. Establish `triv : ∀ N : Subgroup Γ, N.Normal → (N : Set Γ) ⊆ H → ∀ k ∈ N, ∀ y : Γ ⧸ H, k • y = y`. Introduce `N hN hNH k hk y`. Take `⟨z, rfl⟩` from `QuotientGroup.mk_surjective y`. Use `show ((k * z : Γ) : Γ ⧸ H) = z`.

Apply `QuotientGroup.eq.2` to reduce the goal to its premises. Apply `hNH` to reduce the goal to its premises. Use `hN.conj_mem k⁻¹ (N.inv_mem hk) z⁻¹` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Establish `lc : ∀ {X : Type} [TopologicalSpace X] [DiscreteTopology X] (F : Γ → X) (N : Subgroup Γ), IsOpen (N : Set Γ) → (∀ g, ∀ k ∈ N, F (g * k) = F g) → Continuous F`.

Introduce `X _ _ F N hN hF`. Rewrite using `[continuous_discrete_rng]`. Introduce `b`. Rewrite using `[isOpen_iff_forall_mem_open]`. Introduce `g hg`.

Use `⟨(fun k => g⁻¹ * k) ⁻¹' (N : Set Γ), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `k hk`. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff] at hg ⊢`. Use `hF g _ hk` as an intermediate fact. Simplify `this` using `[hg]`.

Conclude with `hN.preimage (continuous_const.mul continuous_id)`. Use `show g⁻¹ * g ∈ (N : Set Γ)`. Simplify using `[N.one_mem]`. Set `M` to `Γ ⧸ H → ZMod n`. Use `letI : TopologicalSpace M := ⊥`.

Use `haveI : DiscreteTopology M := ⟨rfl⟩`. Set `ρ` to `permR (ZMod n) H`. Take `⟨N0, hN0n, hN0o, hN0H⟩` from `getN (H : Set Γ) ⟨Subgroup.isClosed_of_isOpen H hH, hH⟩ H.one_mem`. Establish `ρmul : ∀ g, ∀ k ∈ N0, ρ (g * k) = ρ g`. Introduce `g k hk`.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `f`. Use function extensionality and compare the values at `x`. Use `show f ((g * k)⁻¹ • x) = f (g⁻¹ • x)`. Rewrite using `[_root_.mul_inv_rev, mul_smul, triv N0 hN0n hN0H k⁻¹ (N0.inv_mem hk)]`.

Establish `hcont : ContAction ρ` using `by show Continuous fun p : Γ × M => ρ p.1 p.2`. Rewrite using `[continuous_discrete_rng]`. Introduce `b`. Rewrite using `[isOpen_iff_forall_mem_open]`. Introduce and unpack `⟨g, f⟩ hg`.

Use `⟨((fun k => g⁻¹ * k) ⁻¹' (N0 : Set Γ)) ×ˢ {f}, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨k, f'⟩ ⟨hk, hf'⟩`. Simplify using `only [Set.mem_singleton_iff] at hf'`. Substitute `hf'` using the available equality. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff] at hg ⊢`.

Rewrite using `[← hg]`. Establish `e : k = g * (g⁻¹ * k)` using `by group`. Rewrite using `[e, ρmul g _ hk]`. Conclude with `(hN0o.preimage (continuous_const.mul continuous_id)).prod (isOpen_discrete _)`. Conclude with `⟨by show g⁻¹ * g ∈ (N0 : Set Γ); simp [N0.one_mem], rfl⟩`.

Set `c : (H →* Multiplicative (ZMod n)) → Γ → M` to `fun φ g x => Multiplicative.toAdd (φ ⟨(x.out)⁻¹ * g * (g⁻¹ • x).out, sec_mem H g x⟩)`. Establish `hcoc : ∀ φ : H →* Multiplicative (ZMod n), ∀ g h, c φ (g * h) = c φ g + ρ g (c φ h)`. Introduce `φ g h`. Use function extensionality and compare the values at `x`. Use `show Multiplicative.toAdd (φ ⟨_, sec_mem H (g * h) x⟩) = Multiplicative.toAdd (φ ⟨_, sec_mem H g x⟩) + Multiplicative.toAdd (φ ⟨_, sec_mem H h (g⁻¹ • x)⟩)`.

Rewrite using `[← toAdd_mul, ← map_mul]`. Use `congr 2`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Subgroup.coe_mul, _root_.mul_inv_rev, mul_smul]`. Use `group`.

Establish `hZ : ∀ φ : H →* Multiplicative (ZMod n), IsOpen (φ.ker : Set H) → c φ ∈ Z1 ρ`. Introduce `φ hφ`. Use `show Continuous (c φ) ∧ ∀ g h, c φ (g * h) = c φ g + ρ g (c φ h)`. Use `⟨?_, hcoc φ⟩` and prove the remaining obligations. Set `K : Subgroup Γ` to `φ.ker.map H.subtype`.

Establish `hKo : IsOpen (K : Set Γ)`. Simplify using `only [K]`. Rewrite using `[Subgroup.coe_map, Subgroup.coe_subtype]`. Conclude with `hH.isOpenMap_subtype_val _ hφ`. Establish `hKH : (K : Set Γ) ⊆ H`.

Introduce `k hk`. Take `⟨y, _, rfl⟩` from `Subgroup.mem_map.1 hk`. Conclude with `y.2`. Take `⟨N, hNn, hNo, hNK⟩` from `getN (K : Set Γ) ⟨Subgroup.isClosed_of_isOpen K hKo, hKo⟩ K.one_mem`. Establish `hk0 : ∀ k ∈ N, c φ k = 0`.

Introduce `k hk`. Use function extensionality and compare the values at `x`. Establish `hfix : k⁻¹ • x = x` using `triv N hNn (hNK.trans hKH) k⁻¹ (N.inv_mem hk) x`. Establish `hmem : (x.out)⁻¹ * k * (k⁻¹ • x).out ∈ K`. Rewrite using `[hfix]`.

Apply `hNK` to reduce the goal to its premises. Use `hNn.conj_mem k hk (x.out)⁻¹` as an intermediate fact. Simplify using `using this`. Take `⟨y, hy, hye⟩` from `Subgroup.mem_map.1 hmem`. Use `show Multiplicative.toAdd (φ ⟨_, sec_mem H k x⟩) = 0`.

Establish `hyy : (⟨_, sec_mem H k x⟩ : H) = y` using `Subtype.ext hye.symm`. Rewrite using `[hyy, MonoidHom.mem_ker.1 hy]`. Both sides reduce to the same expression. Apply `lc (c φ) N hNo` to reduce the goal to its premises. Introduce `g k hk`.

Rewrite using `[hcoc φ g k, hk0 k hk, map_zero, add_zero]`. Set `F : {φ : H →* Multiplicative (ZMod n) // IsOpen (φ.ker : Set H)} → H1 ρ` to `fun φ => Submodule.Quotient.mk ⟨c φ.1, hZ φ.1 φ.2⟩`. Establish `hfin : Finite (H1 ρ)` using `h M ρ hcont`. Use `Finite.of_injective F ?_` and prove the remaining obligations. Introduce and unpack `⟨φ, hφ⟩ ⟨ψ, hψ⟩ hEq`.

Establish `hq` using `(Submodule.Quotient.eq _).1 hEq`. Rewrite `hq` using `[Submodule.mem_comap]`. Take `⟨m, hm⟩` from `LinearMap.mem_range.1 hq`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `MonoidHom.ext` to reduce the goal to its premises.

Introduce `h`. Set `x0 : Γ ⧸ H` to `((1 : Γ) : Γ ⧸ H)`. Establish `hfix : (h : Γ)⁻¹ • x0 = x0` using `by show (((h : Γ)⁻¹ * 1 : Γ) : Γ ⧸ H) = ((1 : Γ) : Γ ⧸ H)`. Apply `QuotientGroup.eq.2` to reduce the goal to its premises. Simplify using `using h.2`.

Establish `ht : x0.out ∈ H`. Establish `e : ((x0.out : Γ) : Γ ⧸ H) = ((1 : Γ) : Γ ⧸ H)` using `QuotientGroup.out_eq' x0`. Use `QuotientGroup.eq.1 e` as an intermediate fact. Simplify using `using this`. Establish `hval : ∀ χ : H →* Multiplicative (ZMod n), c χ h x0 = Multiplicative.toAdd (χ h)`.

Introduce `χ`. Use `show Multiplicative.toAdd (χ ⟨_, sec_mem H h x0⟩) = _`. Establish `hel : (⟨_, sec_mem H h x0⟩ : H) = (⟨x0.out, ht⟩ : H)⁻¹ * h * ⟨x0.out, ht⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[hfix]`.

Rewrite using `[hel]`. Use `congr 1`. Rewrite using `[map_mul, map_mul, map_inv, mul_comm (χ ⟨x0.out, ht⟩)⁻¹ (χ h), mul_assoc, inv_mul_cancel, mul_one]`. Establish `hx` using `congrFun (congrFun hm h) x0`. Establish `hL : (d0 ρ m) h x0 = 0` using `by show m ((h : Γ)⁻¹ • x0) - m x0 = 0`.

Rewrite using `[hfix, sub_self]`. Establish `hR : (d0 ρ m) h x0 = c φ h x0 - c ψ h x0` using `hx`. Establish `hcc : c φ h x0 = c ψ h x0` using `sub_eq_zero.1 (hR.symm.trans hL)`. Rewrite `hcc` using `[hval φ, hval ψ]`. Conclude with `hcc`.
-/
private theorem phi_condition_of_finite_cohomology {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (n : ℕ)
    [NeZero n]
    (h : ∀ (M : Type) [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]
      (ρ : Representation (ZMod n) Γ M), ContAction ρ → Finite (H1 ρ)) : PhiCond Γ n := by
  classical
  intro H hH
  haveI : Finite (Γ ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  have getN : ∀ W : Set Γ, IsClopen W → (1 : Γ) ∈ W →
      ∃ N : Subgroup Γ, N.Normal ∧ IsOpen (N : Set Γ) ∧ (N : Set Γ) ⊆ W := by
    intro W hW h1
    obtain ⟨N, hN⟩ := IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one hW h1
    exact ⟨N.toOpenSubgroup, N.isNormal', N.toOpenSubgroup.isOpen, hN⟩
  have triv : ∀ N : Subgroup Γ, N.Normal → (N : Set Γ) ⊆ H → ∀ k ∈ N, ∀ y : Γ ⧸ H, k • y = y := by
    intro N hN hNH k hk y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    show ((k * z : Γ) : Γ ⧸ H) = z
    apply QuotientGroup.eq.2
    apply hNH
    have := hN.conj_mem k⁻¹ (N.inv_mem hk) z⁻¹
    simpa [mul_assoc] using this
  have lc : ∀ {X : Type} [TopologicalSpace X] [DiscreteTopology X] (F : Γ → X) (N : Subgroup Γ),
      IsOpen (N : Set Γ) → (∀ g, ∀ k ∈ N, F (g * k) = F g) → Continuous F := by
    intro X _ _ F N hN hF
    rw [continuous_discrete_rng]
    intro b
    rw [isOpen_iff_forall_mem_open]
    intro g hg
    refine ⟨(fun k => g⁻¹ * k) ⁻¹' (N : Set Γ), ?_, ?_, ?_⟩
    · intro k hk
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hg ⊢
      have := hF g _ hk
      simpa [hg] using this
    · exact hN.preimage (continuous_const.mul continuous_id)
    · show g⁻¹ * g ∈ (N : Set Γ)
      simp [N.one_mem]
  let M := Γ ⧸ H → ZMod n
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  let ρ := permR (ZMod n) H
  obtain ⟨N0, hN0n, hN0o, hN0H⟩ := getN (H : Set Γ) ⟨Subgroup.isClosed_of_isOpen H hH, hH⟩ H.one_mem
  have ρmul : ∀ g, ∀ k ∈ N0, ρ (g * k) = ρ g := by
    intro g k hk
    apply LinearMap.ext
    intro f
    funext x
    show f ((g * k)⁻¹ • x) = f (g⁻¹ • x)
    rw [_root_.mul_inv_rev, mul_smul, triv N0 hN0n hN0H k⁻¹ (N0.inv_mem hk)]
  have hcont : ContAction ρ := by
    show Continuous fun p : Γ × M => ρ p.1 p.2
    rw [continuous_discrete_rng]
    intro b
    rw [isOpen_iff_forall_mem_open]
    rintro ⟨g, f⟩ hg
    refine ⟨((fun k => g⁻¹ * k) ⁻¹' (N0 : Set Γ)) ×ˢ {f}, ?_, ?_, ?_⟩
    · rintro ⟨k, f'⟩ ⟨hk, hf'⟩
      simp only [Set.mem_singleton_iff] at hf'
      subst hf'
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hg ⊢
      rw [← hg]
      have e : k = g * (g⁻¹ * k) := by group
      rw [e, ρmul g _ hk]
    · exact (hN0o.preimage (continuous_const.mul continuous_id)).prod (isOpen_discrete _)
    · exact ⟨by show g⁻¹ * g ∈ (N0 : Set Γ); simp [N0.one_mem], rfl⟩
  let c : (H →* Multiplicative (ZMod n)) → Γ → M := fun φ g x =>
    Multiplicative.toAdd (φ ⟨(x.out)⁻¹ * g * (g⁻¹ • x).out, sec_mem H g x⟩)
  have hcoc : ∀ φ : H →* Multiplicative (ZMod n), ∀ g h, c φ (g * h) = c φ g + ρ g (c φ h) := by
    intro φ g h
    funext x
    show Multiplicative.toAdd (φ ⟨_, sec_mem H (g * h) x⟩) =
      Multiplicative.toAdd (φ ⟨_, sec_mem H g x⟩) + Multiplicative.toAdd (φ ⟨_, sec_mem H h (g⁻¹ • x)⟩)
    rw [← toAdd_mul, ← map_mul]
    congr 2
    apply Subtype.ext
    simp only [Subgroup.coe_mul, _root_.mul_inv_rev, mul_smul]
    group
  have hZ : ∀ φ : H →* Multiplicative (ZMod n), IsOpen (φ.ker : Set H) → c φ ∈ Z1 ρ := by
    intro φ hφ
    show Continuous (c φ) ∧ ∀ g h, c φ (g * h) = c φ g + ρ g (c φ h)
    refine ⟨?_, hcoc φ⟩
    let K : Subgroup Γ := φ.ker.map H.subtype
    have hKo : IsOpen (K : Set Γ) := by
      simp only [K]
      rw [Subgroup.coe_map, Subgroup.coe_subtype]
      exact hH.isOpenMap_subtype_val _ hφ
    have hKH : (K : Set Γ) ⊆ H := by
      intro k hk
      obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.1 hk
      exact y.2
    obtain ⟨N, hNn, hNo, hNK⟩ := getN (K : Set Γ) ⟨Subgroup.isClosed_of_isOpen K hKo, hKo⟩ K.one_mem
    have hk0 : ∀ k ∈ N, c φ k = 0 := by
      intro k hk
      funext x
      have hfix : k⁻¹ • x = x := triv N hNn (hNK.trans hKH) k⁻¹ (N.inv_mem hk) x
      have hmem : (x.out)⁻¹ * k * (k⁻¹ • x).out ∈ K := by
        rw [hfix]
        apply hNK
        have := hNn.conj_mem k hk (x.out)⁻¹
        simpa using this
      obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.1 hmem
      show Multiplicative.toAdd (φ ⟨_, sec_mem H k x⟩) = 0
      have hyy : (⟨_, sec_mem H k x⟩ : H) = y := Subtype.ext hye.symm
      rw [hyy, MonoidHom.mem_ker.1 hy]
      rfl
    apply lc (c φ) N hNo
    intro g k hk
    rw [hcoc φ g k, hk0 k hk, map_zero, add_zero]
  let F : {φ : H →* Multiplicative (ZMod n) // IsOpen (φ.ker : Set H)} → H1 ρ :=
    fun φ => Submodule.Quotient.mk ⟨c φ.1, hZ φ.1 φ.2⟩
  have hfin : Finite (H1 ρ) := h M ρ hcont
  refine Finite.of_injective F ?_
  rintro ⟨φ, hφ⟩ ⟨ψ, hψ⟩ hEq
  have hq := (Submodule.Quotient.eq _).1 hEq
  rw [Submodule.mem_comap] at hq
  obtain ⟨m, hm⟩ := LinearMap.mem_range.1 hq
  apply Subtype.ext
  apply MonoidHom.ext
  intro h
  let x0 : Γ ⧸ H := ((1 : Γ) : Γ ⧸ H)
  have hfix : (h : Γ)⁻¹ • x0 = x0 := by
    show (((h : Γ)⁻¹ * 1 : Γ) : Γ ⧸ H) = ((1 : Γ) : Γ ⧸ H)
    apply QuotientGroup.eq.2
    simpa using h.2
  have ht : x0.out ∈ H := by
    have e : ((x0.out : Γ) : Γ ⧸ H) = ((1 : Γ) : Γ ⧸ H) := QuotientGroup.out_eq' x0
    have := QuotientGroup.eq.1 e
    simpa using this
  have hval : ∀ χ : H →* Multiplicative (ZMod n), c χ h x0 = Multiplicative.toAdd (χ h) := by
    intro χ
    show Multiplicative.toAdd (χ ⟨_, sec_mem H h x0⟩) = _
    have hel : (⟨_, sec_mem H h x0⟩ : H) = (⟨x0.out, ht⟩ : H)⁻¹ * h * ⟨x0.out, ht⟩ := by
      apply Subtype.ext
      simp [hfix]
    rw [hel]
    congr 1
    rw [map_mul, map_mul, map_inv, mul_comm (χ ⟨x0.out, ht⟩)⁻¹ (χ h), mul_assoc, inv_mul_cancel, mul_one]
  have hx := congrFun (congrFun hm h) x0
  have hL : (d0 ρ m) h x0 = 0 := by
    show m ((h : Γ)⁻¹ • x0) - m x0 = 0
    rw [hfix, sub_self]
  have hR : (d0 ρ m) h x0 = c φ h x0 - c ψ h x0 := hx
  have hcc : c φ h x0 = c ψ h x0 := sub_eq_zero.1 (hR.symm.trans hL)
  rw [hval φ, hval ψ] at hcc
  exact hcc

/- English proof (translation)
Introduce `hGF Ω _ _ _ l _ S hS`. Use `haveI : IsClosed ((NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) : Set (G ℚ Ω))) := isClosed_NS Ω _`. Use `⟨?_, inferInstance, inferInstance, totDisc_quot _ (isClosed_NS Ω _)⟩` and prove the remaining obligations. Use `haveI : NeZero (l ^ 1) := ⟨pow_ne_zero 1 (Fact.out : l.Prime).ne_zero⟩`. Establish `key` using `phi_condition_of_finite_cohomology (Γ := GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) (l ^ 1) (fun M _ _ _ _ _ ρ hc => (hGF ℚ Ω l 1 M S ρ one_pos hS hc).2.1)`.

Rewrite `key` using `[pow_one]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.galois_group_phi_condition :
    GlobalFiniteness → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 ℚ))), ContainsAbove S l →
          PhiCond (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) l ∧ CompactSpace (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) ∧ T2Space (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) ∧ TotallyDisconnectedSpace (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) := by
  intro hGF Ω _ _ _ l _ S hS
  haveI : IsClosed ((NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) : Set (G ℚ Ω))) := isClosed_NS Ω _
  refine ⟨?_, inferInstance, inferInstance, totDisc_quot _ (isClosed_NS Ω _)⟩
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero 1 (Fact.out : l.Prime).ne_zero⟩
  have key := phi_condition_of_finite_cohomology (Γ := GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) (l ^ 1)
    (fun M _ _ _ _ _ ρ hc => (hGF ℚ Ω l 1 M S ρ one_pos hS hc).2.1)
  rwa [pow_one] at key
