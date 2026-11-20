import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.DenseGenericOfFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCycAwayHomComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectOddLevelRigid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectLoweredLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLevelChangeBySymplecticSimilitudeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectPullbackLevelPowerCalculusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticSimilitudeInvertibleModNStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowSection

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegAct

variable {h n N : ℕ} {F : SFam h N (zetaAway N)} {j : cycAway n →+* cycAway N}

/- English proof (translation)
The claim follows from `Subtype.ext (Complex.isPrimitiveRoot_exp N hN).pow_eq_one`.
-/
theorem zeta_pow (hN : N ≠ 0) : zetaAway N ^ N = 1 :=
  Subtype.ext (Complex.isPrimitiveRoot_exp N hN).pow_eq_one

/- English proof (translation)
The claim follows from `Nat.coprime_one_left N root := (pow_one _).symm fix := RingHom.id_comp j symp x y := by simp [Int.ModEq] low x := rfl comm := by rw [spMap_id', Category.id_comp, Category.comp_id] map := by obtain ⟨φ, φ₂, a, b, c, d⟩ := GlobalTheory.SiegelPullComp.pb_id F.univ exact ⟨φ, a, ⟨φ₂, b …`.
-/
theorem twist_one : Twist F j LinearMap.id 1 (RingHom.id _) (𝟙 _) where
  cop := Nat.coprime_one_left N
  root := (pow_one _).symm
  fix := RingHom.id_comp j
  symp x y := by simp [Int.ModEq]
  low x := rfl
  comm := by rw [spMap_id', Category.id_comp, Category.comp_id]
  map := by
    obtain ⟨φ, φ₂, a, b, c, d⟩ := GlobalTheory.SiegelPullComp.pb_id F.univ
    exact ⟨φ, a, ⟨φ₂, b, c⟩, d⟩

/- English proof (translation)
The claim follows from `Nat.Coprime.mul t.cop t'.cop root := by rw [RingHom.comp_apply, t'.root, map_pow, t.root, ← pow_mul, mul_comm] fix := by rw [RingHom.comp_assoc, t'.fix, t.fix] symp x y := by have h1 := t.symp (T' x) (T' y) have h2 := (t'.symp x y).mul_left m simp only [LinearMap.comp_apply] calc …`.
-/
theorem Twist.mul {T T' : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)} {m m' : ℕ}
    {σ σ' : cycAway N →+* cycAway N} {f f' : F.X ⟶ F.X} (t : Twist F j T m σ f) (t' : Twist F j T' m' σ' f') :
    Twist F j (T ∘ₗ T') (m * m') (σ.comp σ') (f ≫ f') where
  cop := Nat.Coprime.mul t.cop t'.cop
  root := by rw [RingHom.comp_apply, t'.root, map_pow, t.root, ← pow_mul, mul_comm]
  fix := by rw [RingHom.comp_assoc, t'.fix, t.fix]
  symp x y := by
    have h1 := t.symp (T' x) (T' y)
    have h2 := (t'.symp x y).mul_left m
    simp only [LinearMap.comp_apply]
    calc _ ≡ m * omegaStd (T' x) (T' y) [ZMOD N] := h1
      _ ≡ m * (m' * omegaStd x y) [ZMOD N] := h2
      _ = ((m * m' : ℕ) : ℤ) * omegaStd x y := by push_cast; ring
  low x := by simp only [LinearMap.comp_apply]; rw [t.low, t'.low]
  comm := by rw [Category.assoc, t'.comm, ← Category.assoc, t.comm, Category.assoc, spMap_comp']
  map := by
    obtain ⟨ν, a, b, c⟩ := t.map
    obtain ⟨ν', a', b', c'⟩ := t'.map
    refine ⟨ν ≫ ν', a.comp a', Sq.comp b' b, fun x => ?_⟩
    simp only [LinearMap.comp_apply]
    rw [← Category.assoc, c, Category.assoc, c', ← Category.assoc]

/- English proof (translation)
Take `⟨ν, a, ⟨ν₂, b, c⟩, d⟩` from `t.map`. Conclude with `⟨ν, ν₂, a, b, c, d⟩`.
-/
theorem Twist.siegPB {T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)} {m : ℕ} {σ : cycAway N →+* cycAway N}
    {f : F.X ⟶ F.X} (t : Twist F j T m σ f) (hN : N ≠ 0) (hinj : ∀ a, (∃ b, T a = N • b) → ∃ b, a = N • b)
    (hsurj : ∀ a, ∃ a' b, T a' = a + N • b) :
    SiegPB (relabel F.univ T σ hN (zeta_pow hN) t.root t.symp hinj hsurj) F.univ f := by
  obtain ⟨ν, a, ⟨ν₂, b, c⟩, d⟩ := t.map
  exact ⟨ν, ν₂, a, b, c, d⟩

/- English proof (translation)
Take `⟨hinj, hsurj, -⟩` from `GlobalTheory.T.symplecticSimilitude_invertible_modN h N m T hN cop symp`. Take `⟨hr, hd⟩` from `F.isReduced_and_dense`. Take `⟨f, hf, H⟩` from `F.rep F.X (F.s ≫ spMap σ) (relabel F.univ T σ hN (zeta_pow hN) root symp hinj hsurj) hr (hd.mono fun x hx => by`. Establish `hx' : (F.s x).asIdeal = ⊥` using `hx`. Use `show ((F.s ≫ spMap σ) x).asIdeal = ⊥`.

Rewrite using `[Scheme.Hom.comp_apply]`. Express the relevant statement in the definitionally equal form `((F.s x).asIdeal).comap σ = ⊥`. Rewrite using `[hx']`. Conclude with `Ideal.comap_bot_of_injective σ hσi) F.princ`. Take `⟨ν, ν₂, a, b, c, d⟩` from `H`.

Conclude with `⟨f, cop, root, fix, symp, low, hf, ν, a, ⟨ν₂, b, c⟩, d⟩`.
-/
theorem exists_twist (hN : N ≠ 0) {T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)} {m : ℕ}
    {σ : cycAway N →+* cycAway N} (hσi : Function.Injective σ) (cop : m.Coprime N)
    (root : σ (zetaAway N) = zetaAway N ^ m) (fix : σ.comp j = j)
    (symp : ∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N])
    (low : ∀ x, F.univ.lev (T x) ^ (N / n) = F.univ.lev x ^ (N / n)) : ∃ f, Twist F j T m σ f := by
  obtain ⟨hinj, hsurj, -⟩ := GlobalTheory.T.symplecticSimilitude_invertible_modN h N m T hN cop symp
  obtain ⟨hr, hd⟩ := F.isReduced_and_dense
  obtain ⟨f, hf, H⟩ := F.rep F.X (F.s ≫ spMap σ) (relabel F.univ T σ hN (zeta_pow hN) root symp hinj hsurj) hr
    (hd.mono fun x hx => by
      have hx' : (F.s x).asIdeal = ⊥ := hx
      show ((F.s ≫ spMap σ) x).asIdeal = ⊥
      rw [Scheme.Hom.comp_apply]
      change ((F.s x).asIdeal).comap σ = ⊥
      rw [hx']
      exact Ideal.comap_bot_of_injective σ hσi) F.princ
  obtain ⟨ν, ν₂, a, b, c, d⟩ := H
  exact ⟨f, cop, root, fix, symp, low, hf, ν, a, ⟨ν₂, b, c⟩, d⟩

/- English proof (translation)
Take `⟨hinj, hsurj, -⟩` from `GlobalTheory.T.symplecticSimilitude_invertible_modN h N m T hN t.cop t.symp`. Use `F.hom_ext (relabel F.univ T σ hN (zeta_pow hN) t.root t.symp hinj hsurj) f f' (by rw [t.comm, t'.comm, hσ]) (t.siegPB hN hinj hsurj) ?_` and prove the remaining obligations. Take `⟨ν, a, ⟨ν₂, b, c⟩, d⟩` from `t'.map`. Conclude with `⟨ν, ν₂, a, b, c, fun x => (congrArg (fun z => z.left ≫ ν) (hT x)).trans (d x)⟩`.
-/
theorem Twist.unique (hN : N ≠ 0) {T T' : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)} {m m' : ℕ}
    {σ σ' : cycAway N →+* cycAway N} {f f' : F.X ⟶ F.X} (t : Twist F j T m σ f) (t' : Twist F j T' m' σ' f')
    (hσ : σ = σ') (hT : ∀ x, F.univ.lev (T x) = F.univ.lev (T' x)) : f = f' := by
  obtain ⟨hinj, hsurj, -⟩ := GlobalTheory.T.symplecticSimilitude_invertible_modN h N m T hN t.cop t.symp
  refine F.hom_ext (relabel F.univ T σ hN (zeta_pow hN) t.root t.symp hinj hsurj) f f' (by rw [t.comm, t'.comm, hσ])
    (t.siegPB hN hinj hsurj) ?_
  obtain ⟨ν, a, ⟨ν₂, b, c⟩, d⟩ := t'.map
  exact ⟨ν, ν₂, a, b, c, fun x => (congrArg (fun z => z.left ≫ ν) (hT x)).trans (d x)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨a, b, fun x => by have := pow_section a _ _ (c x) (N / n) rw [t.low x] at this exact this⟩`.
-/
theorem Twist.sRelBy {T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)} {m : ℕ} {σ : cycAway N →+* cycAway N}
    {f : F.X ⟶ F.X} {ν : F.univ.A.left ⟶ F.univ.A.left} (t : Twist F j T m σ f)
    (a : IsGrpPullback F.univ.A F.univ.A f ν) (b : Sq F.univ F.univ ν)
    (c : ∀ x, (F.univ.lev (T x)).left ≫ ν = f ≫ (F.univ.lev x).left) :
    SRelBy F.univ F.univ (N / n) (N / n) f ν :=
  ⟨a, b, fun x => by
    have := pow_section a _ _ (c x) (N / n)
    rw [t.low x] at this
    exact this⟩

/- English proof (translation)
Establish `hN0 : N ≠ 0` using `hN.pos.ne'`. Establish `hn0 : n ≠ 0` using `by omega`. Take `⟨c₀, hC0, h0C⟩` from `GlobalTheory.T.exists_siegelObject_lowered_level h n N (cycAway n) (cycAway N) (zetaAway n) (zetaAway N) j F.X F.s F.univ hN0 (isUnit_natCast hN0) hnN hj`. Establish `hc₀ : c₀.Principal` using `(GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h N n n (cycAway N) (cycAway n) (cycAway n) (zetaAway N) (zetaAway n) (zetaAway n) F.X F.X F.X F.s (F.s ≫ spMap j) (F.s ≫ spMap j) F.univ c₀ c₀ (𝟙 _) (𝟙 _) (N / n) 1 1 h0C).2.1 F.princ`. Take `⟨ψ, hψ⟩` from `hC0`.

Establish `e₁` using `sRelBy_comp hψ hφ`. Establish `e₂` using `sRelBy_comp hψ hφ'`. Use `GlobalTheory.SiegRigid.eq_of_sRelBy h n n' (N / n) (cycAway n) B' (cycBase hn0) ζ' F.X S' (F.s ≫ spMap j) s' c₀ c' (g ≫ 𝟙 _) (φ ≫ ψ) (φ' ≫ ψ) hn (hN.of_dvd_nat hnN) hc₀ e₁ e₂` as an intermediate fact. Use `hψ.1.1.hom_ext this ?_` and prove the remaining obligations. Rewrite using `[hφ.1.1.w, hφ'.1.1.w]`.
-/
theorem rig (hn : 3 ≤ n) (hN : Odd N) (hnN : n ∣ N) (hj : j (zetaAway n) = zetaAway N ^ (N / n))
    {n' : ℕ} {B' : Type} [CommRing B'] {ζ' : B'} {S' : Scheme.{0}} {s' : S' ⟶ Sp B'} (c' : SiegPre h n' ζ' s')
    (g : S' ⟶ F.X) (φ φ' : c'.A.left ⟶ F.univ.A.left) (hφ : SRelBy c' F.univ (N / n) (N / n) g φ)
    (hφ' : SRelBy c' F.univ (N / n) (N / n) g φ') : φ = φ' := by
  have hN0 : N ≠ 0 := hN.pos.ne'
  have hn0 : n ≠ 0 := by omega
  obtain ⟨c₀, hC0, h0C⟩ := GlobalTheory.T.exists_siegelObject_lowered_level h n N (cycAway n) (cycAway N) (zetaAway n) (zetaAway N) j F.X F.s F.univ
    hN0 (isUnit_natCast hN0) hnN hj
  have hc₀ : c₀.Principal := (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h N n n (cycAway N) (cycAway n) (cycAway n) (zetaAway N) (zetaAway n)
    (zetaAway n) F.X F.X F.X F.s (F.s ≫ spMap j) (F.s ≫ spMap j) F.univ c₀ c₀ (𝟙 _) (𝟙 _) (N / n) 1 1 h0C).2.1 F.princ
  obtain ⟨ψ, hψ⟩ := hC0
  have e₁ := sRelBy_comp hψ hφ
  have e₂ := sRelBy_comp hψ hφ'
  have := GlobalTheory.SiegRigid.eq_of_sRelBy h n n' (N / n) (cycAway n) B' (cycBase hn0) ζ' F.X S' (F.s ≫ spMap j) s' c₀ c'
    (g ≫ 𝟙 _) (φ ≫ ψ) (φ' ≫ ψ) hn (hN.of_dvd_nat hnN) hc₀ e₁ e₂
  refine hψ.1.1.hom_ext this ?_
  rw [hφ.1.1.w, hφ'.1.1.w]

end GlobalTheory.SiegAct

namespace GlobalTheory.SiegAct

section Calc2

variable {h n n' n'' : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}
  {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n'' ζ'' s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
  {d d' d'' : ℕ}

/- English proof (translation)
The claim follows from `((GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n'' B B' B'' ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f' d d' d'' h₁).1).1 h₂`.
-/
theorem sRel_comp (h₁ : SRel c' c d' d f) (h₂ : SRel c'' c' d'' d' f') : SRel c'' c d'' d (f' ≫ f) :=
  ((GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n'' B B' B'' ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f' d d' d'' h₁).1).1 h₂

/- English proof (translation)
The claim follows from `((GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n'' B B' B'' ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f' d d' d'' h₁).1).2 h₂`.
-/
theorem sRel_cancel (h₁ : SRel c' c d' d f) (h₂ : SRel c'' c d'' d (f' ≫ f)) : SRel c'' c' d'' d' f' :=
  ((GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n'' B B' B'' ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f' d d' d'' h₁).1).2 h₂

/- English proof (translation)
Simplify using `using (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n' B B' B' ζ ζ' ζ' S S' S' s s' s' c c' c' f (𝟙 S') 1 1 1 h₁).2.2 e`.
-/
theorem sRel_scale (h₁ : SRel c' c 1 1 f) (e : ℕ) : SRel c' c e e f := by
  simpa using (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n' B B' B' ζ ζ' ζ' S S' S' s s' s' c c' c' f (𝟙 S') 1 1 1 h₁).2.2 e

end Calc2

variable {h n N : ℕ} {F : SFam h N (zetaAway N)} {j : cycAway n →+* cycAway N}

/- English proof (translation)
Establish `hp` using `isPrimitiveRoot_map hN β`. Establish `hpos : 0 < N` using `Nat.pos_of_ne_zero hN`. Rewrite `e` using `[pow_eq_pow_mod a hp.pow_eq_one, pow_eq_pow_mod b hp.pow_eq_one]`. Rewrite using `[pow_eq_pow_mod a (zeta_pow hN), pow_eq_pow_mod b (zeta_pow hN), hp.pow_inj (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) e]`.
-/
theorem zeta_pow_congr (hN : N ≠ 0) {K : Type} [Field K] (β : cycAway N →+* K) {a b : ℕ}
    (e : β (zetaAway N) ^ a = β (zetaAway N) ^ b) : zetaAway N ^ a = zetaAway N ^ b := by
  have hp := isPrimitiveRoot_map hN β
  have hpos : 0 < N := Nat.pos_of_ne_zero hN
  rw [pow_eq_pow_mod a hp.pow_eq_one, pow_eq_pow_mod b hp.pow_eq_one] at e
  rw [pow_eq_pow_mod a (zeta_pow hN), pow_eq_pow_mod b (zeta_pow hN),
    hp.pow_inj (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) e]

/- English proof (translation)
Take `⟨p, -, hp1, -, -, hp4⟩` from `hCy`. Establish `e : y ≫ (F.univ.lev v).left = y ≫ (1 : 𝟙_ (Over F.X) ⟶ F.univ.A).left`. Use `pow_section hp1 _ _ (hp4 v) 0` as an intermediate fact. Rewrite `this` using `[pow_zero, pow_zero]`. Rewrite using `[← hp4 v, hv, ← this]`.

Set `K` to `AlgebraicClosure (IsLocalRing.ResidueField R)`. Set `z : Sp K ⟶ Sp R` to `spMap ((algebraMap (IsLocalRing.ResidueField R) K).comp (IsLocalRing.residue R))`. Take `⟨β, hβ⟩` from `exists_spMap ((z ≫ y) ≫ F.s)`. Set `u : Kˣ` to `Units.ofPowEqOne (β (zetaAway N)) N (by rw [← map_pow, zeta_pow hN, map_one]) hN`. Take `⟨g1, -, -⟩` from `F.univ.geom K (z ≫ y) β u hβ rfl`.

Use `(g1 v).1 (Over.OverMorphism.ext ?_)` and prove the remaining obligations. Rewrite using `[unit_left', Category.assoc, e, ← Category.assoc, ← unit_left', MonObj.comp_one]`.
-/
theorem exists_eq_nsmul_of_pull (hN : N ≠ 0) {R : Type} [CommRing R] [IsLocalRing R] {B' : Type} [CommRing B']
    {ζ' : B'} {s' : Sp R ⟶ Sp B'} (y : Sp R ⟶ F.X) (Cy : SiegPre h N ζ' s') (hCy : SiegPB Cy F.univ y)
    (v : Fin h ⊕ Fin h → ℤ) (hv : Cy.lev v = 1) : ∃ b, v = N • b := by
  obtain ⟨p, -, hp1, -, -, hp4⟩ := hCy
  have e : y ≫ (F.univ.lev v).left = y ≫ (1 : 𝟙_ (Over F.X) ⟶ F.univ.A).left := by
    have := pow_section hp1 _ _ (hp4 v) 0
    rw [pow_zero, pow_zero] at this
    rw [← hp4 v, hv, ← this]
  let K := AlgebraicClosure (IsLocalRing.ResidueField R)
  let z : Sp K ⟶ Sp R := spMap ((algebraMap (IsLocalRing.ResidueField R) K).comp (IsLocalRing.residue R))
  obtain ⟨β, hβ⟩ := exists_spMap ((z ≫ y) ≫ F.s)
  let u : Kˣ := Units.ofPowEqOne (β (zetaAway N)) N (by rw [← map_pow, zeta_pow hN, map_one]) hN
  obtain ⟨g1, -, -⟩ := F.univ.geom K (z ≫ y) β u hβ rfl
  refine (g1 v).1 (Over.OverMorphism.ext ?_)
  rw [unit_left', Category.assoc, e, ← Category.assoc, ← unit_left', MonObj.comp_one]

/- English proof (translation)
Establish `hN0 : N ≠ 0` using `hN.pos.ne'`. Take `⟨β, hβ⟩` from `exists_spMap (y ≫ F.s)`. Establish `hσβ : β.comp σ = β` using `spMap_inj (by rw [← spMap_comp', ← hβ, Category.assoc, ← t.comm, ← Category.assoc, hy])`. Establish `e : β (zetaAway N) ^ m = β (zetaAway N) ^ 1`. Rewrite using `[pow_one, ← map_pow, ← t.root, ← RingHom.comp_apply, hσβ]`.

Establish `hσ1 : σ = RingHom.id _` using `(cycAway_galois N hN0).2.1 _ σ (RingHom.id _) (by`. Rewrite using `[t.root, RingHom.id_apply, zeta_pow_congr hN0 β e, pow_one])`. Take `⟨ν, a, b, c⟩` from `t.map`. Take `⟨Cy, hCy⟩` from `(GlobalTheory.siegPre_pullback h N (cycAway N) (zetaAway N) F.X (Sp k) F.s (y ≫ F.s) y F.univ rfl).1`. Take `⟨p, p₂, hp1, hp2, hp3, hp4⟩` from `hCy`.

Establish `hpd : SRelBy Cy F.univ (N / n) (N / n) y p` using `⟨hp1, ⟨p₂, hp2, hp3⟩, fun x => pow_section hp1 _ _ (hp4 x) _⟩`. Establish `h2 : SRelBy Cy F.univ (N / n) (N / n) y (p ≫ ν)`. Use `sRelBy_comp (t.sRelBy a b c) hpd` as an intermediate fact. Rewrite `this` using `[hy]`. Then use the resulting hypothesis. Establish `hpp : p = p ≫ ν` using `rig hn hN hnN hj Cy y p (p ≫ ν) hpd h2`.

Establish `hlev : ∀ x, y ≫ (F.univ.lev (T x)).left = y ≫ (F.univ.lev x).left` using `fun x => by`. Combine the equalities or inequalities in the displayed calculation. Set `z : kˣ` to `Units.ofPowEqOne (β (zetaAway N)) N (by rw [← map_pow, zeta_pow hN0, map_one]) hN0`. Take `⟨g1, -, -⟩` from `F.univ.geom k y β z hβ rfl`. Establish `hT : ∀ x, F.univ.lev (T x) = F.univ.lev x` using `fun x => by`.

Establish `e1 : toUnit (Over.mk y) ≫ F.univ.lev (T x) = toUnit (Over.mk y) ≫ F.univ.lev x` using `Over.OverMorphism.ext (by rw [unit_left', unit_left', hlev])`. Establish `e2 : toUnit (Over.mk y) ≫ F.univ.lev (T x - x) = 1`. Use `F.univ.lev_add (T x - x) x` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Rewrite `e1` using `[this, MonObj.comp_mul]`.

Conclude with `mul_eq_right.1 e1`. Take `⟨b', hb'⟩` from `(g1 _).1 e2`. Rewrite using `[← sub_add_cancel (T x) x, F.univ.lev_add, hb', lev_N_smul, _root_.one_mul]`. Conclude with `t.unique hN0 twist_one hσ1 hT`.
-/
theorem Twist.eq_id_of_fixed (hn : 3 ≤ n) (hN : Odd N) (hnN : n ∣ N) (hj : j (zetaAway n) = zetaAway N ^ (N / n))
    {T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)} {m : ℕ} {σ : cycAway N →+* cycAway N} {f : F.X ⟶ F.X}
    (t : Twist F j T m σ f) {k : Type} [Field k] [IsAlgClosed k] (y : Sp k ⟶ F.X) (hy : y ≫ f = y) : f = 𝟙 _ := by
  have hN0 : N ≠ 0 := hN.pos.ne'
  obtain ⟨β, hβ⟩ := exists_spMap (y ≫ F.s)
  have hσβ : β.comp σ = β :=
    spMap_inj (by rw [← spMap_comp', ← hβ, Category.assoc, ← t.comm, ← Category.assoc, hy])
  have e : β (zetaAway N) ^ m = β (zetaAway N) ^ 1 := by
    rw [pow_one, ← map_pow, ← t.root, ← RingHom.comp_apply, hσβ]
  have hσ1 : σ = RingHom.id _ := (cycAway_galois N hN0).2.1 _ σ (RingHom.id _) (by
    rw [t.root, RingHom.id_apply, zeta_pow_congr hN0 β e, pow_one])
  obtain ⟨ν, a, b, c⟩ := t.map
  obtain ⟨Cy, hCy⟩ := (GlobalTheory.siegPre_pullback h N (cycAway N) (zetaAway N) F.X (Sp k) F.s (y ≫ F.s) y F.univ rfl).1
  obtain ⟨p, p₂, hp1, hp2, hp3, hp4⟩ := hCy
  have hpd : SRelBy Cy F.univ (N / n) (N / n) y p := ⟨hp1, ⟨p₂, hp2, hp3⟩, fun x => pow_section hp1 _ _ (hp4 x) _⟩
  have h2 : SRelBy Cy F.univ (N / n) (N / n) y (p ≫ ν) := by
    have := sRelBy_comp (t.sRelBy a b c) hpd
    rwa [hy] at this
  have hpp : p = p ≫ ν := rig hn hN hnN hj Cy y p (p ≫ ν) hpd h2
  have hlev : ∀ x, y ≫ (F.univ.lev (T x)).left = y ≫ (F.univ.lev x).left := fun x => by
    calc y ≫ (F.univ.lev (T x)).left = (Cy.lev (T x)).left ≫ p := (hp4 _).symm
      _ = (Cy.lev (T x)).left ≫ p ≫ ν := by rw [← hpp]
      _ = y ≫ (F.univ.lev (T x)).left ≫ ν := by rw [← Category.assoc, hp4, Category.assoc]
      _ = y ≫ (F.univ.lev x).left := by rw [c, ← Category.assoc, hy]
  let z : kˣ := Units.ofPowEqOne (β (zetaAway N)) N (by rw [← map_pow, zeta_pow hN0, map_one]) hN0
  obtain ⟨g1, -, -⟩ := F.univ.geom k y β z hβ rfl
  have hT : ∀ x, F.univ.lev (T x) = F.univ.lev x := fun x => by
    have e1 : toUnit (Over.mk y) ≫ F.univ.lev (T x) = toUnit (Over.mk y) ≫ F.univ.lev x :=
      Over.OverMorphism.ext (by rw [unit_left', unit_left', hlev])
    have e2 : toUnit (Over.mk y) ≫ F.univ.lev (T x - x) = 1 := by
      have := F.univ.lev_add (T x - x) x
      rw [sub_add_cancel] at this
      rw [this, MonObj.comp_mul] at e1
      exact mul_eq_right.1 e1
    obtain ⟨b', hb'⟩ := (g1 _).1 e2
    rw [← sub_add_cancel (T x) x, F.univ.lev_add, hb', lev_N_smul, _root_.one_mul]
  exact t.unique hN0 twist_one hσ1 hT

end GlobalTheory.SiegAct

namespace GlobalTheory.SiegAct

variable {h n N : ℕ} {F : SFam h N (zetaAway N)} {j : cycAway n →+* cycAway N}

/- English proof (translation)
Establish `hN0 : N ≠ 0` using `hN.pos.ne'`. Establish `hn0 : n ≠ 0` using `by omega`. Take `⟨β, hβ⟩` from `exists_spMap (y ≫ F.s)`. Take `⟨β', hβ'⟩` from `exists_spMap (y' ≫ F.s)`. Establish `G` using `cycAway_galois N hN0`.

Take `⟨m, hmc, hm⟩` from `G.2.2 R β β'`. Take `⟨σ, hσ⟩` from `G.1 m hmc`. Take `⟨Cy, hCy⟩` from `(GlobalTheory.siegPre_pullback h N (cycAway N) (zetaAway N) F.X (Sp R) F.s (spMap β) y F.univ hβ).1`. Take `⟨Cy', hCy'⟩` from `(GlobalTheory.siegPre_pullback h N (cycAway N) (zetaAway N) F.X (Sp R) F.s (spMap β') y' F.univ hβ').1`. Establish `k1 : SRel Cy F.univ (N / n) (N / n) y` using `sRel_scale ((sRel_one_one_iff _ _ _).2 hCy) _`.

Establish `k1' : SRel Cy' F.univ (N / n) (N / n) y'` using `sRel_scale ((sRel_one_one_iff _ _ _).2 hCy') _`. Establish `a1 : SRel c Cy 1 (N / n) (𝟙 _)` using `sRel_cancel k1 (by rwa [Category.id_comp])`. Establish `a1' : SRel c Cy' 1 (N / n) (𝟙 _)` using `sRel_cancel k1' (by rwa [Category.id_comp])`. Establish `idCy' : SRel Cy' Cy' (N / n) (N / n) (𝟙 _ ≫ 𝟙 _)`. Rewrite using `[Category.comp_id]`.

Conclude with `sRel_scale ((sRel_one_one_iff _ _ _).2 (GlobalTheory.SiegelPullComp.pb_id Cy')) _`. Establish `a2 : SRel Cy' c (N / n) 1 (𝟙 _)` using `sRel_cancel a1' idCy'`. Establish `a3 : SRel Cy' Cy (N / n) (N / n) (𝟙 _ ≫ 𝟙 _)` using `sRel_comp a1 a2`. Rewrite `a3` using `[Category.comp_id]`. Take `⟨φ, hφ, ⟨φ₂, hsq, hP⟩, hl⟩` from `a3`.

Take `⟨T, hTω, hTl⟩` from `(GlobalTheory.T.siegel_level_change_by_symplectic_similitude h N (cycAway N) (cycBase hN0) hN).2 R β m β' Cy Cy' φ φ₂ hm hφ hsq hP`. Establish `low : ∀ x, F.univ.lev (T x) ^ (N / n) = F.univ.lev x ^ (N / n)` using `fun x => by`. Establish `e1` using `pow_section hφ _ _ ((hTl x).trans (Category.id_comp _).symm) (N / n)`. Establish `e2 : Cy.lev (T x) ^ (N / n) = Cy.lev x ^ (N / n)` using `Over.OverMorphism.ext (by`. Use `e1.symm.trans (hl x)` as an intermediate fact.

Rewrite using `[Category.id_comp, Category.id_comp] at this)` and apply the resulting hypothesis. Establish `e3 : Cy.lev ((N / n) • (T x - x)) = 1`. Use `Cy.lev_add ((N / n) • (T x - x)) ((N / n) • x)` as an intermediate fact. Rewrite `this` using `[← smul_add, sub_add_cancel, lev_nsmul Cy (N / n) (T x), lev_nsmul Cy (N / n) x, e2]`. Conclude with `mul_eq_right.1 this.symm`.

Take `⟨b, hb⟩` from `exists_eq_nsmul_of_pull hN0 y Cy hCy _ e3`. Establish `e4` using `F.univ.lev_add ((N / n) • (T x - x)) ((N / n) • x)`. Rewrite `e4` using `[← smul_add, sub_add_cancel, lev_nsmul F.univ (N / n) (T x), lev_nsmul F.univ (N / n) x, hb, lev_N_smul, _root_.one_mul]`. Conclude with `e4`. Establish `hbj : β.comp j = β'.comp j` using `spMap_inj (by`.

Rewrite using `[← spMap_comp', ← spMap_comp', ← hβ, ← hβ', Category.assoc, Category.assoc, hs])`. Set `r` to `IsLocalRing.residue R`. Establish `e5 : (r.comp β) (zetaAway N) ^ (N / n) = (r.comp β) (zetaAway N) ^ (m * (N / n))`. Use `congrArg r (RingHom.congr_fun hbj (zetaAway n))` as an intermediate fact. Simplify using `only [RingHom.comp_apply, hj, map_pow, hm] at this`.

Rewrite using `[RingHom.comp_apply, this, pow_mul]`. Establish `e6` using `zeta_pow_congr hN0 (r.comp β) e5`. Establish `fix : σ.toRingHom.comp j = j` using `(cycAway_galois n hn0).2.1 _ _ _ (by`. Rewrite using `[RingHom.comp_apply, hj, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, map_pow, hσ, ← pow_mul, e6])`. Take `⟨f, t⟩` from `exists_twist (F := F) hN0 σ.injective hmc hσ fix hTω low`.

Take `⟨hinj, hsurj, -⟩` from `GlobalTheory.T.symplecticSimilitude_invertible_modN h N m T hN0 hmc hTω`. Establish `X0 : SiegPB Cy' (relabel Cy T σ.toRingHom hN0 (zeta_pow hN0) hσ hTω hinj hsurj) (𝟙 _)` using `⟨φ, φ₂, hφ, hsq, hP, fun x => (hTl x).trans (Category.id_comp _).symm⟩`. Take `⟨p, p₂, hp1, hp2, hp3, hp4⟩` from `hCy`. Establish `X1 : SiegPB (relabel Cy T σ.toRingHom hN0 (zeta_pow hN0) hσ hTω hinj hsurj) (relabel F.univ T σ.toRingHom hN0 (zeta_pow hN0) hσ hTω hinj hsurj) y` using `⟨p, p₂, hp1, hp2, hp3, fun x => hp4 (T x)⟩`. Establish `X2` using `GlobalTheory.SiegelPullComp.pb_comp (GlobalTheory.SiegelPullComp.pb_comp (t.siegPB hN0 hinj hsurj) X1) X0`.

Rewrite `X2` using `[Category.id_comp]`. Establish `hbs : β.comp σ.toRingHom = β'` using `G.2.1 R _ _ (by`. Rewrite using `[RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ, map_pow, hm])`. Use `⟨T, m, σ.toRingHom, f, t, F.inj R (y ≫ f) y' (spMap β') Cy' ?_ X2 hCy'⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, t.comm, ← Category.assoc, hβ, spMap_comp', hbs, hβ']`.
-/
theorem exists_twist_of_points (hn : 3 ≤ n) (hN : Odd N) (hnN : n ∣ N) (hj : j (zetaAway n) = zetaAway N ^ (N / n))
    (R : Type) [CommRing R] [IsLocalRing R] (y y' : Sp R ⟶ F.X) (s' : Sp R ⟶ Sp (cycAway n))
    (c : SiegPre h n (zetaAway n) s') (hs : y ≫ F.s ≫ spMap j = y' ≫ F.s ≫ spMap j)
    (hy : SRel c F.univ 1 (N / n) y) (hy' : SRel c F.univ 1 (N / n) y') :
    ∃ T m σ f, Twist F j T m σ f ∧ y ≫ f = y' := by
  have hN0 : N ≠ 0 := hN.pos.ne'
  have hn0 : n ≠ 0 := by omega
  obtain ⟨β, hβ⟩ := exists_spMap (y ≫ F.s)
  obtain ⟨β', hβ'⟩ := exists_spMap (y' ≫ F.s)
  have G := cycAway_galois N hN0
  obtain ⟨m, hmc, hm⟩ := G.2.2 R β β'
  obtain ⟨σ, hσ⟩ := G.1 m hmc
  obtain ⟨Cy, hCy⟩ := (GlobalTheory.siegPre_pullback h N (cycAway N) (zetaAway N) F.X (Sp R) F.s (spMap β) y F.univ hβ).1
  obtain ⟨Cy', hCy'⟩ := (GlobalTheory.siegPre_pullback h N (cycAway N) (zetaAway N) F.X (Sp R) F.s (spMap β') y' F.univ hβ').1
  have k1 : SRel Cy F.univ (N / n) (N / n) y := sRel_scale ((sRel_one_one_iff _ _ _).2 hCy) _
  have k1' : SRel Cy' F.univ (N / n) (N / n) y' := sRel_scale ((sRel_one_one_iff _ _ _).2 hCy') _
  have a1 : SRel c Cy 1 (N / n) (𝟙 _) := sRel_cancel k1 (by rwa [Category.id_comp])
  have a1' : SRel c Cy' 1 (N / n) (𝟙 _) := sRel_cancel k1' (by rwa [Category.id_comp])
  have idCy' : SRel Cy' Cy' (N / n) (N / n) (𝟙 _ ≫ 𝟙 _) := by
    rw [Category.comp_id]; exact sRel_scale ((sRel_one_one_iff _ _ _).2 (GlobalTheory.SiegelPullComp.pb_id Cy')) _
  have a2 : SRel Cy' c (N / n) 1 (𝟙 _) := sRel_cancel a1' idCy'
  have a3 : SRel Cy' Cy (N / n) (N / n) (𝟙 _ ≫ 𝟙 _) := sRel_comp a1 a2
  rw [Category.comp_id] at a3
  obtain ⟨φ, hφ, ⟨φ₂, hsq, hP⟩, hl⟩ := a3
  obtain ⟨T, hTω, hTl⟩ := (GlobalTheory.T.siegel_level_change_by_symplectic_similitude h N (cycAway N) (cycBase hN0) hN).2 R β m β' Cy Cy' φ φ₂ hm hφ hsq hP

  have low : ∀ x, F.univ.lev (T x) ^ (N / n) = F.univ.lev x ^ (N / n) := fun x => by
    have e1 := pow_section hφ _ _ ((hTl x).trans (Category.id_comp _).symm) (N / n)
    have e2 : Cy.lev (T x) ^ (N / n) = Cy.lev x ^ (N / n) := Over.OverMorphism.ext (by
      have := e1.symm.trans (hl x)
      rwa [Category.id_comp, Category.id_comp] at this)
    have e3 : Cy.lev ((N / n) • (T x - x)) = 1 := by
      have := Cy.lev_add ((N / n) • (T x - x)) ((N / n) • x)
      rw [← smul_add, sub_add_cancel, lev_nsmul Cy (N / n) (T x), lev_nsmul Cy (N / n) x, e2] at this
      exact mul_eq_right.1 this.symm
    obtain ⟨b, hb⟩ := exists_eq_nsmul_of_pull hN0 y Cy hCy _ e3
    have e4 := F.univ.lev_add ((N / n) • (T x - x)) ((N / n) • x)
    rw [← smul_add, sub_add_cancel, lev_nsmul F.univ (N / n) (T x), lev_nsmul F.univ (N / n) x, hb, lev_N_smul,
      _root_.one_mul] at e4
    exact e4

  have hbj : β.comp j = β'.comp j := spMap_inj (by
    rw [← spMap_comp', ← spMap_comp', ← hβ, ← hβ', Category.assoc, Category.assoc, hs])
  let r := IsLocalRing.residue R
  have e5 : (r.comp β) (zetaAway N) ^ (N / n) = (r.comp β) (zetaAway N) ^ (m * (N / n)) := by
    have := congrArg r (RingHom.congr_fun hbj (zetaAway n))
    simp only [RingHom.comp_apply, hj, map_pow, hm] at this
    rw [RingHom.comp_apply, this, pow_mul]
  have e6 := zeta_pow_congr hN0 (r.comp β) e5
  have fix : σ.toRingHom.comp j = j := (cycAway_galois n hn0).2.1 _ _ _ (by
    rw [RingHom.comp_apply, hj, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, map_pow, hσ, ← pow_mul, e6])
  obtain ⟨f, t⟩ := exists_twist (F := F) hN0 σ.injective hmc hσ fix hTω low
  obtain ⟨hinj, hsurj, -⟩ := GlobalTheory.T.symplecticSimilitude_invertible_modN h N m T hN0 hmc hTω
  have X0 : SiegPB Cy' (relabel Cy T σ.toRingHom hN0 (zeta_pow hN0) hσ hTω hinj hsurj) (𝟙 _) :=
    ⟨φ, φ₂, hφ, hsq, hP, fun x => (hTl x).trans (Category.id_comp _).symm⟩
  obtain ⟨p, p₂, hp1, hp2, hp3, hp4⟩ := hCy
  have X1 : SiegPB (relabel Cy T σ.toRingHom hN0 (zeta_pow hN0) hσ hTω hinj hsurj)
      (relabel F.univ T σ.toRingHom hN0 (zeta_pow hN0) hσ hTω hinj hsurj) y :=
    ⟨p, p₂, hp1, hp2, hp3, fun x => hp4 (T x)⟩
  have X2 := GlobalTheory.SiegelPullComp.pb_comp (GlobalTheory.SiegelPullComp.pb_comp (t.siegPB hN0 hinj hsurj) X1) X0
  rw [Category.id_comp] at X2
  have hbs : β.comp σ.toRingHom = β' := G.2.1 R _ _ (by
    rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ, map_pow, hm])
  refine ⟨T, m, σ.toRingHom, f, t, F.inj R (y ≫ f) y' (spMap β') Cy' ?_ X2 hCy'⟩
  rw [Category.assoc, t.comm, ← Category.assoc, hβ, spMap_comp', hbs, hβ']

end GlobalTheory.SiegAct

namespace GlobalTheory.SiegAct

variable {h n N : ℕ} {F : SFam h N (zetaAway N)} {j : cycAway n →+* cycAway N}

/- English proof (translation)
Take `⟨-, -, T', hT', hω'⟩` from `GlobalTheory.T.symplecticSimilitude_invertible_modN h N m T hN t.cop t.symp`. Use `haveI : NeZero N := ⟨hN⟩`. Use `set m' : ℕ := (((ZMod.unitOfCoprime m t.cop)⁻¹ : (ZMod N)ˣ) : ZMod N).val with hm'`. Establish `hmm : m * m' ≡ 1 [MOD N]`. Use `(ZMod.natCast_eq_natCast_iff _ _ _).1 ?_` and prove the remaining obligations.

Rewrite using `[Nat.cast_mul, hm', ZMod.natCast_zmod_val, Nat.cast_one, ← ZMod.coe_unitOfCoprime m t.cop]`. Conclude with `Units.mul_inv _`. Establish `cop' : m'.Coprime N` using `Nat.coprime_of_mul_modEq_one m (by rwa [mul_comm])`. Establish `G` using `cycAway_galois N hN`. Take `⟨σ', hσ'⟩` from `G.1 m' cop'`.

Establish `hz1 : zetaAway N ^ (m * m') = zetaAway N`. Rewrite using `[pow_eq_pow_mod (m * m') (zeta_pow hN), show m * m' % N = 1 % N from hmm, ← pow_eq_pow_mod 1 (zeta_pow hN), pow_one]`. Establish `hfix : zetaAway N ^ (m * (N / n)) = zetaAway N ^ (N / n)`. Use `RingHom.congr_fun t.fix (zetaAway n)` as an intermediate fact. Rewrite `this` using `[RingHom.comp_apply, hj, map_pow, t.root, ← pow_mul]`. Then use the resulting hypothesis.

Establish `fix' : σ'.toRingHom.comp j = j` using `(cycAway_galois n hn0).2.1 _ _ _ (by`. Rewrite using `[RingHom.comp_apply, hj, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, map_pow, hσ', ← pow_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hTT : ∀ x, F.univ.lev (T (T' x)) = F.univ.lev x` using `fun x => by`. Take `⟨b, hb⟩` from `hT' x`.

Rewrite using `[hb, F.univ.lev_add, lev_N_smul, _root_.mul_one]`. Take `⟨f', t'⟩` from `exists_twist (F := F) hN σ'.injective cop' hσ' fix' (hω' m' hmm) (fun x => by rw [← t.low (T' x), hTT])`. Use `⟨T', m', σ'.toRingHom, f', t', (t.mul t').unique hN twist_one ?_ hTT⟩` and prove the remaining obligations. Conclude with `G.2.1 _ _ _ (by`. Rewrite using `[RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', map_pow, t.root, ← pow_mul, hz1, RingHom.id_apply])`.
-/
theorem Twist.exists_inv (hN : N ≠ 0) (hN1 : 1 < N) (hn0 : n ≠ 0) (hj : j (zetaAway n) = zetaAway N ^ (N / n))
    {T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)} {m : ℕ} {σ : cycAway N →+* cycAway N} {f : F.X ⟶ F.X}
    (t : Twist F j T m σ f) :
    ∃ (T' : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)) (m' : ℕ) (σ' : cycAway N →+* cycAway N) (f' : F.X ⟶ F.X),
      Twist F j T' m' σ' f' ∧ f ≫ f' = 𝟙 _ := by
  obtain ⟨-, -, T', hT', hω'⟩ := GlobalTheory.T.symplecticSimilitude_invertible_modN h N m T hN t.cop t.symp
  haveI : NeZero N := ⟨hN⟩
  set m' : ℕ := (((ZMod.unitOfCoprime m t.cop)⁻¹ : (ZMod N)ˣ) : ZMod N).val with hm'
  have hmm : m * m' ≡ 1 [MOD N] := by
    refine (ZMod.natCast_eq_natCast_iff _ _ _).1 ?_
    rw [Nat.cast_mul, hm', ZMod.natCast_zmod_val, Nat.cast_one, ← ZMod.coe_unitOfCoprime m t.cop]
    exact Units.mul_inv _
  have cop' : m'.Coprime N := Nat.coprime_of_mul_modEq_one m (by rwa [mul_comm])
  have G := cycAway_galois N hN
  obtain ⟨σ', hσ'⟩ := G.1 m' cop'
  have hz1 : zetaAway N ^ (m * m') = zetaAway N := by
    rw [pow_eq_pow_mod (m * m') (zeta_pow hN), show m * m' % N = 1 % N from hmm,
      ← pow_eq_pow_mod 1 (zeta_pow hN), pow_one]
  have hfix : zetaAway N ^ (m * (N / n)) = zetaAway N ^ (N / n) := by
    have := RingHom.congr_fun t.fix (zetaAway n)
    rwa [RingHom.comp_apply, hj, map_pow, t.root, ← pow_mul] at this
  have fix' : σ'.toRingHom.comp j = j := (cycAway_galois n hn0).2.1 _ _ _ (by
    rw [RingHom.comp_apply, hj, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, map_pow, hσ', ← pow_mul]
    calc zetaAway N ^ (m' * (N / n)) = (zetaAway N ^ (m * (N / n))) ^ m' := by rw [hfix, ← pow_mul, mul_comm]
      _ = (zetaAway N ^ (m * m')) ^ (N / n) := by rw [← pow_mul, ← pow_mul]; congr 1; ring
      _ = zetaAway N ^ (N / n) := by rw [hz1])
  have hTT : ∀ x, F.univ.lev (T (T' x)) = F.univ.lev x := fun x => by
    obtain ⟨b, hb⟩ := hT' x
    rw [hb, F.univ.lev_add, lev_N_smul, _root_.mul_one]
  obtain ⟨f', t'⟩ := exists_twist (F := F) hN σ'.injective cop' hσ' fix' (hω' m' hmm)
    (fun x => by rw [← t.low (T' x), hTT])
  refine ⟨T', m', σ'.toRingHom, f', t', (t.mul t').unique hN twist_one ?_ hTT⟩
  exact G.2.1 _ _ _ (by
    rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', map_pow, t.root, ← pow_mul, hz1,
      RingHom.id_apply])

variable (F j) in

def Grp : Type := {f : F.X ⟶ F.X // ∃ T m σ, Twist F j T m σ f}

instance : One (Grp F j) := ⟨⟨𝟙 _, _, _, _, twist_one⟩⟩

instance : Mul (Grp F j) := ⟨fun a c => ⟨a.1 ≫ c.1, by
  obtain ⟨T, m, σ, t⟩ := a.2
  obtain ⟨T', m', σ', t'⟩ := c.2
  exact ⟨_, _, _, t.mul t'⟩⟩⟩

/- English proof (translation)
Take `⟨T, m, σ, t⟩` from `a.2`. Take `⟨T', m', σ', f', t', e⟩` from `t.exists_inv hN hN1 hn0 hj`. Conclude with `⟨⟨f', T', m', σ', t'⟩, Subtype.ext e⟩`.
-/
theorem Grp.exists_inv (hN : N ≠ 0) (hN1 : 1 < N) (hn0 : n ≠ 0) (hj : j (zetaAway n) = zetaAway N ^ (N / n))
    (a : Grp F j) : ∃ c : Grp F j, a * c = 1 := by
  obtain ⟨T, m, σ, t⟩ := a.2
  obtain ⟨T', m', σ', f', t', e⟩ := t.exists_inv hN hN1 hn0 hj
  exact ⟨⟨f', T', m', σ', t'⟩, Subtype.ext e⟩

@[reducible] def Grp.group (hN : N ≠ 0) (hN1 : 1 < N) (hn0 : n ≠ 0) (hj : j (zetaAway n) = zetaAway N ^ (N / n)) :
    Group (Grp F j) :=
  letI : Inv (Grp F j) := ⟨fun a => (Grp.exists_inv hN hN1 hn0 hj a).choose⟩
  Group.ofRightAxioms (fun _ _ _ => Subtype.ext (Category.assoc _ _ _)) (fun _ => Subtype.ext (Category.comp_id _))
    fun a => (Grp.exists_inv hN hN1 hn0 hj a).choose_spec

/- English proof (translation)
Establish `hd : ∀ k, (N : ℤ) ∣ v k - w k` using `fun k => (ZMod.intCast_eq_intCast_iff_dvd_sub (w k) (v k) N).1 (e k).symm`. Establish `: v = w + N • fun k => (v k - w k) / N`. Use function extensionality and compare the values at `k`. Rewrite using `[Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Int.mul_ediv_cancel' (hd k)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, C.lev_add, lev_N_smul, _root_.mul_one]`.
-/
theorem lev_eq_of_cast {B : Type} [CommRing B] {ζ : B} {S : Scheme.{0}} {s : S ⟶ Sp B} (C : SiegPre h N ζ s)
    {v w : Fin h ⊕ Fin h → ℤ} (e : ∀ k, ((v k : ℤ) : ZMod N) = ((w k : ℤ) : ZMod N)) : C.lev v = C.lev w := by
  have hd : ∀ k, (N : ℤ) ∣ v k - w k := fun k => (ZMod.intCast_eq_intCast_iff_dvd_sub (w k) (v k) N).1 (e k).symm
  have : v = w + N • fun k => (v k - w k) / N := by
    funext k
    rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Int.mul_ediv_cancel' (hd k)]
    ring
  rw [this, C.lev_add, lev_N_smul, _root_.mul_one]

/- English proof (translation)
Use `haveI : NeZero N := ⟨hN⟩`. Use `choose T m σ t using fun a : Grp F j => a.2`. Establish `key : ∀ (U : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)) x k, ((U x k : ℤ) : ZMod N) = ∑ i, ((x i : ℤ) : ZMod N) * ((U (fun l => if i = l then 1 else 0) k : ℤ) : ZMod N)`. Introduce `U x k`. Use `conv_lhs => rw [LinearMap.pi_apply_eq_sum_univ U x]`.

Simplify using `[Finset.sum_apply]`. Use `Finite.of_injective (β := (Fin h ⊕ Fin h → Fin h ⊕ Fin h → ZMod N) × ZMod N) (fun a => (fun i k => (((T a) (fun l => if i = l then 1 else 0) k : ℤ) : ZMod N), (m a : ZMod N))) fun a c hac => Subtype.ext ?_` and prove the remaining obligations. Simplify using `only [Prod.mk.injEq] at hac`. Take `⟨h1, h2⟩` from `hac`. Use `(t a).unique hN (t c) ?_ fun x => lev_eq_of_cast F.univ fun k => ?_` and prove the remaining obligations.

Apply `(cycAway_galois N hN).2.1` to reduce the goal to its premises. Rewrite using `[(t a).root, (t c).root, pow_eq_pow_mod (m a) (zeta_pow hN), pow_eq_pow_mod (m c) (zeta_pow hN), (ZMod.natCast_eq_natCast_iff' _ _ _).1 h2]`. Rewrite using `[key, key]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [congrFun (congrFun h1 i) k]`.
-/
theorem Grp.finite (hN : N ≠ 0) : Finite (Grp F j) := by
  haveI : NeZero N := ⟨hN⟩
  choose T m σ t using fun a : Grp F j => a.2
  have key : ∀ (U : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)) x k, ((U x k : ℤ) : ZMod N) =
      ∑ i, ((x i : ℤ) : ZMod N) * ((U (fun l => if i = l then 1 else 0) k : ℤ) : ZMod N) := by
    intro U x k
    conv_lhs => rw [LinearMap.pi_apply_eq_sum_univ U x]
    simp [Finset.sum_apply]
  refine Finite.of_injective (β := (Fin h ⊕ Fin h → Fin h ⊕ Fin h → ZMod N) × ZMod N)
    (fun a => (fun i k => (((T a) (fun l => if i = l then 1 else 0) k : ℤ) : ZMod N), (m a : ZMod N)))
    fun a c hac => Subtype.ext ?_
  simp only [Prod.mk.injEq] at hac
  obtain ⟨h1, h2⟩ := hac
  refine (t a).unique hN (t c) ?_ fun x => lev_eq_of_cast F.univ fun k => ?_
  · apply (cycAway_galois N hN).2.1
    rw [(t a).root, (t c).root, pow_eq_pow_mod (m a) (zeta_pow hN), pow_eq_pow_mod (m c) (zeta_pow hN),
      (ZMod.natCast_eq_natCast_iff' _ _ _).1 h2]
  · rw [key, key]
    exact Finset.sum_congr rfl fun i _ => by rw [congrFun (congrFun h1 i) k]

/- English proof (translation)
Introduce `h n N F j hn hN hnN hj`. Establish `hN0 : N ≠ 0` using `hN.pos.ne'`. Establish `hn0 : n ≠ 0` using `by omega`. Establish `hN1 : 1 < N` using `by have := Nat.le_of_dvd hN.pos hnN; omega`. Use `letI G := Grp.group (F := F) (j := j) hN0 hN1 hn0 hj`.

Establish `hν : ∀ a : Grp F j, ∃ ν : F.univ.A.left ⟶ F.univ.A.left, SRelBy F.univ F.univ (N / n) (N / n) a.1 ν` using `fun a => by`. Take `⟨T, m, σ, t⟩` from `a.2`. Take `⟨ν, x, y, z⟩` from `t.map`. Conclude with `⟨ν, t.sRelBy x y z⟩`. Use `choose ν hν using hν`.

Establish `idpb : SRelBy F.univ F.univ (N / n) (N / n) (𝟙 _) (𝟙 _)` using `⟨⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => (mul_left_congr (G := F.univ.A) (Category.comp_id T.hom) x₀ y₀ x y (hx.trans (Category.comp_id _)) (hy.trans (Category.comp_id _))).trans (Category.comp_id _).symm⟩, ⟨𝟙 _, ⟨by simp, by simp⟩, GlobalTheory.SiegelPullC …`. Use `⟨Grp F j, G, Grp.finite hN0, fun a => a.1, ν, rfl, fun _ _ => rfl, ?_, fun a c => ?_, fun a => ?_, hν, fun k _ _ y a hy => ?_, fun R _ _ y y' s' c hs h1 h2 => ?_⟩` and prove the remaining obligations. Conclude with `rig hn hN hnN hj F.univ (𝟙 _) _ _ (hν 1) idpb`. Conclude with `rig hn hN hnN hj F.univ _ _ _ (hν (a * c)) (sRelBy_comp (hν c) (hν a))`. Take `⟨T, m, σ, t⟩` from `a.2`.

Rewrite using `[← Category.assoc, t.comm, Category.assoc, spMap_comp', t.fix]`. Take `⟨T, m, σ, t⟩` from `a.2`. Conclude with `Subtype.ext (t.eq_id_of_fixed hn hN hnN hj y hy)`. Take `⟨T, m, σ, f, t, e⟩` from `exists_twist_of_points hn hN hnN hj R y y' s' c hs h1 h2`. Conclude with `⟨⟨f, T, m, σ, t⟩, e⟩`.
-/
theorem siegel_group_action : ∀ (h n N : ℕ) (F : SFam h N (zetaAway N)) (j : cycAway n →+* cycAway N), 3 ≤ n → Odd N → n ∣ N → j (zetaAway n) = zetaAway N ^ (N / n) → ∃ (Ga : Type) (_ : Group Ga) (_ : Finite Ga) (ρ : Ga → (F.X ⟶ F.X)) (ν : Ga → (F.univ.A.left ⟶ F.univ.A.left)), ρ 1 = 𝟙 _ ∧ (∀ a c, ρ (a * c) = ρ a ≫ ρ c) ∧ ν 1 = 𝟙 _ ∧ (∀ a c, ν (a * c) = ν a ≫ ν c) ∧ (∀ a, ρ a ≫ F.s ≫ spMap j = F.s ≫ spMap j) ∧ (∀ a, SRelBy F.univ F.univ (N / n) (N / n) (ρ a) (ν a)) ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ F.X) (a : Ga), y ≫ ρ a = y → a = 1) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (y y' : Sp R ⟶ F.X) (s' : Sp R ⟶ Sp (cycAway n)) (c : SiegPre h n (zetaAway n) s'), y ≫ F.s ≫ spMap j = y' ≫ F.s ≫ spMap j → SRel c F.univ 1 (N / n) y → SRel c F.univ 1 (N / n) y' → ∃ a, y ≫ ρ a = y' := by
  intro h n N F j hn hN hnN hj
  have hN0 : N ≠ 0 := hN.pos.ne'
  have hn0 : n ≠ 0 := by omega
  have hN1 : 1 < N := by have := Nat.le_of_dvd hN.pos hnN; omega
  letI G := Grp.group (F := F) (j := j) hN0 hN1 hn0 hj
  have hν : ∀ a : Grp F j, ∃ ν : F.univ.A.left ⟶ F.univ.A.left, SRelBy F.univ F.univ (N / n) (N / n) a.1 ν :=
    fun a => by
      obtain ⟨T, m, σ, t⟩ := a.2
      obtain ⟨ν, x, y, z⟩ := t.map
      exact ⟨ν, t.sRelBy x y z⟩
  choose ν hν using hν
  have idpb : SRelBy F.univ F.univ (N / n) (N / n) (𝟙 _) (𝟙 _) :=
    ⟨⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy =>
      (mul_left_congr (G := F.univ.A) (Category.comp_id T.hom) x₀ y₀ x y (hx.trans (Category.comp_id _))
        (hy.trans (Category.comp_id _))).trans (Category.comp_id _).symm⟩,
      ⟨𝟙 _, ⟨by simp, by simp⟩, GlobalTheory.SiegelPullComp.iso_pull_id F.univ.isLB⟩, fun x => by simp⟩
  refine ⟨Grp F j, G, Grp.finite hN0, fun a => a.1, ν, rfl, fun _ _ => rfl, ?_, fun a c => ?_, fun a => ?_, hν,
    fun k _ _ y a hy => ?_, fun R _ _ y y' s' c hs h1 h2 => ?_⟩
  · exact rig hn hN hnN hj F.univ (𝟙 _) _ _ (hν 1) idpb
  · exact rig hn hN hnN hj F.univ _ _ _ (hν (a * c)) (sRelBy_comp (hν c) (hν a))
  · obtain ⟨T, m, σ, t⟩ := a.2
    rw [← Category.assoc, t.comm, Category.assoc, spMap_comp', t.fix]
  · obtain ⟨T, m, σ, t⟩ := a.2
    exact Subtype.ext (t.eq_id_of_fixed hn hN hnN hj y hy)
  · obtain ⟨T, m, σ, f, t, e⟩ := exists_twist_of_points hn hN hnN hj R y y' s' c hs h1 h2
    exact ⟨⟨f, T, m, σ, t⟩, e⟩

end GlobalTheory.SiegAct
