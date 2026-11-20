import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.XiMulNu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
import ReciprocityTheory.DualLattices.AinfFacts
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValuationCoeEqNorm

noncomputable section

open WittVector Ideal CategoryTheory Opposite Function

namespace GlobalTheory

open PDivGroup Sandwich

namespace Published

section At

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

def PrismaticDieudonneHodgeAt (ε : PreTilt O p) : Prop :=
  ∃ (M : (PDivGroup p O)ᵒᵖ ⥤ ModuleCat.{0} (Ainf p O)) (D : (PDivGroup p O)ᵒᵖ ⥤ ModuleCat.{0} O)
    (φ : ∀ G : PDivGroup p O,
      M.obj (op G) →ₛₗ[(WittVector.frobenius : Ainf p O →+* Ainf p O)] M.obj (op G))
    (r : ∀ G : PDivGroup p O, M.obj (op G) →ₛₗ[fontaineTheta O p] D.obj (op G))
    (ι : ∀ G : PDivGroup p O, G.omega →ₗ[O] D.obj (op G))
    (π : ∀ G : PDivGroup p O, D.obj (op G) →ₗ[O] G.dual.Lie),

    M.Additive ∧
    (∀ G : PDivGroup p O, Module.Free (Ainf p O) (M.obj (op G)) ∧
      Module.Finite (Ainf p O) (M.obj (op G)) ∧
      Module.finrank (Ainf p O) (M.obj (op G)) = G.height) ∧

    (∀ (G : PDivGroup p O) (m : M.obj (op G)),
      ∃ n, φ G n = (WittVector.frobenius (xi ε) : Ainf p O) • m) ∧
    (∀ (G H : PDivGroup p O) (f : G ⟶ H) (m : M.obj (op H)),
      M.map f.op (φ H m) = φ G (M.map f.op m)) ∧

    (∀ G : PDivGroup p O, Surjective (r G) ∧ ∀ m, r G m = 0 ↔ ∃ n, m = xi ε • n) ∧
    (∀ (G H : PDivGroup p O) (f : G ⟶ H) (m : M.obj (op H)),
      D.map f.op (r H m) = r G (M.map f.op m)) ∧

    (∀ G : PDivGroup p O, Injective (ι G) ∧ Function.Exact (ι G) (π G) ∧ Surjective (π G)) ∧
    (∀ (G H : PDivGroup p O) (f : G ⟶ H) (w : H.omega),
      D.map f.op (ι H w) = ι G (omegaMap G H f w)) ∧
    (∀ (G H : PDivGroup p O) (f : G ⟶ H) (x : D.obj (op H)),
      π G (D.map f.op x) = lieMap H.dual G.dual (dualHom G H f) (π H x)) ∧

    (∃ e : M.obj (op (const p O)) ≃ₗ[Ainf p O] Ainf p O,
      ∀ m, e (φ (const p O) m) = WittVector.frobenius (e m)) ∧
    (∃ e : M.obj (op (PDivGroup.mu p O)) ≃ₗ[Ainf p O] Ainf p O,
      ∀ m, e (φ (PDivGroup.mu p O) m) = WittVector.frobenius (xi ε) * WittVector.frobenius (e m)) ∧

    (∀ g : M.obj (op (PDivGroup.mu p O)) →ₗ[Ainf p O] M.obj (op (const p O)),
      (∀ m, g (φ (PDivGroup.mu p O) m) = φ (const p O) (g m)) →
        ∃! f : const p O ⟶ PDivGroup.mu p O, (M.map f.op).hom = g)

end At

def PrismaticDieudonneHodge : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O] (ε : PreTilt O p),
      IsPrimitiveRoot (root ε).untilt p → PrismaticDieudonneHodgeAt ε

end Published

section Covariant

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

def CovariantDieudonneAt (ε : PreTilt O p) : Prop :=
  ∃ (M : PDivGroup p O ⥤ ModuleCat.{0} (Ainf p O)) (H : PDivGroup p O ⥤ ModuleCat.{0} O)
    (ψ : ∀ G : PDivGroup p O, M.obj G →ₛₗ[phiInv p O] M.obj G)
    (r : ∀ G : PDivGroup p O, M.obj G →ₛₗ[fontaineTheta O p] H.obj G)
    (ι : ∀ G : PDivGroup p O, G.dual.omega →ₗ[O] H.obj G)
    (π : ∀ G : PDivGroup p O, H.obj G →ₗ[O] G.Lie),

    M.Additive ∧
    (∀ G : PDivGroup p O, Module.Free (Ainf p O) (M.obj G) ∧ Module.Finite (Ainf p O) (M.obj G) ∧
      Module.finrank (Ainf p O) (M.obj G) = G.height) ∧

    (∀ G : PDivGroup p O, Injective (ψ G) ∧ ∀ m, ∃ n, ψ G n = xi ε • m) ∧
    (∀ (G G' : PDivGroup p O) (f : G ⟶ G') (m : M.obj G), M.map f (ψ G m) = ψ G' (M.map f m)) ∧

    (∀ G : PDivGroup p O, Surjective (r G) ∧ ∀ m, r G m = 0 ↔ ∃ n, m = xi ε • n) ∧
    (∀ (G G' : PDivGroup p O) (f : G ⟶ G') (m : M.obj G), H.map f (r G m) = r G' (M.map f m)) ∧

    (∀ G : PDivGroup p O, Injective (ι G) ∧ Function.Exact (ι G) (π G) ∧ Surjective (π G)) ∧
    (∀ (G G' : PDivGroup p O) (f : G ⟶ G') (w : G.dual.omega),
      H.map f (ι G w) = ι G' (omegaDualMap G G' f w)) ∧
    (∀ (G G' : PDivGroup p O) (f : G ⟶ G') (x : H.obj G),
      π G' (H.map f x) = lieMap G G' f (π G x)) ∧
    (∀ G : PDivGroup p O, (Module.Free O (H.obj G) ∧ Module.Finite O (H.obj G) ∧
      Module.finrank O (H.obj G) = G.height) ∧
      (Module.Free O G.dual.omega ∧ Module.Finite O G.dual.omega) ∧
      (Module.Free O G.Lie ∧ Module.Finite O G.Lie)) ∧

    ∃ (e₀ : M.obj (const p O) ≃ₗ[Ainf p O] Ainf p O)
      (e₁ : M.obj (PDivGroup.mu p O) ≃ₗ[Ainf p O] Ainf p O) (u : ℤ_[p]ˣ),
      (∀ m, e₀ (ψ (const p O) m) = phiInv p O (e₀ m)) ∧
      (∀ m, e₁ (ψ (PDivGroup.mu p O) m) = xi ε * phiInv p O (e₁ m)) ∧
      ∀ (ζ : ℕ → O) (h0 : ζ 0 = 1) (h : ∀ n, ζ (n + 1) ^ p = ζ n),
        (∀ n, ζ n = (root^[n] ε).untilt) →
          ∀ m, e₁ (M.map (epsHom ζ h0 h) m) = ofPadic p O u * Sandwich.mu ε * e₀ m

end Covariant

namespace Dieudonne

section Linear

variable {A O M D : Type*} [CommRing A] [CommRing O] [AddCommGroup M] [Module A M]
  [AddCommGroup D] [Module O D]

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis A M`. Use `choose s hs using h`. Set `P : Matrix _ _ A` to `Matrix.of fun i j => b.repr (φ (b j)) i`. Establish `key : ∀ m i, b.repr (φ m) i = (P.mulVec fun j => σ (b.repr m j)) i` using `fun m i => by`. Establish `h1 : φ m = ∑ j, σ (b.repr m j) • φ (b j)` using `by conv_lhs => rw [← b.sum_repr m, map_sum]`.

Simplify using `only [map_smulₛₗ]`. Rewrite using `[h1]`. Simplify using `[P, Matrix.mulVec, dotProduct, mul_comm]`. Establish `hP : P * Matrix.of (fun j k => σ (b.repr (s (b k)) j)) = x • 1`. Use extensionality with `i k`.

Use `key (s (b k)) i` as an intermediate fact. Rewrite `this` using `[hs]`. Simplify using `only [Matrix.mulVec, dotProduct] at this`. Simplify using `[Matrix.mul_apply, ← this, Matrix.one_apply, Finsupp.single_apply, eq_comm]`. Establish `hd : P.det ≠ 0` using `fun h0 => by`.

Use `congrArg Matrix.det hP` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one]`. Conclude with `pow_ne_zero _ hx this.symm`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `m hm`.

Establish `h1` using `Matrix.eq_zero_of_mulVec_eq_zero hd (v := fun j => σ (b.repr m j)) (funext fun i => by rw [← key, hm]; simp)`. Use `b.ext_elem fun j => hσ ?_` and prove the remaining obligations. Simplify using `using congrFun h1 j`.
-/
theorem injective_of_smul_mem_range [IsDomain A] [Module.Free A M] [Module.Finite A M]
    {σ : A →+* A} (hσ : Injective σ) (φ : M →ₛₗ[σ] M) {x : A} (hx : x ≠ 0)
    (h : ∀ m, ∃ n, φ n = x • m) : Injective φ := by
  classical
  let b := Module.Free.chooseBasis A M
  choose s hs using h
  let P : Matrix _ _ A := Matrix.of fun i j => b.repr (φ (b j)) i
  have key : ∀ m i, b.repr (φ m) i = (P.mulVec fun j => σ (b.repr m j)) i := fun m i => by
    have h1 : φ m = ∑ j, σ (b.repr m j) • φ (b j) := by
      conv_lhs => rw [← b.sum_repr m, map_sum]
      simp only [map_smulₛₗ]
    rw [h1]
    simp [P, Matrix.mulVec, dotProduct, mul_comm]
  have hP : P * Matrix.of (fun j k => σ (b.repr (s (b k)) j)) = x • 1 := by
    ext i k
    have := key (s (b k)) i
    rw [hs] at this
    simp only [Matrix.mulVec, dotProduct] at this
    simp [Matrix.mul_apply, ← this, Matrix.one_apply, Finsupp.single_apply, eq_comm]
  have hd : P.det ≠ 0 := fun h0 => by
    have := congrArg Matrix.det hP
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
    exact pow_ne_zero _ hx this.symm
  rw [injective_iff_map_eq_zero]
  intro m hm
  have h1 := Matrix.eq_zero_of_mulVec_eq_zero hd (v := fun j => σ (b.repr m j))
    (funext fun i => by rw [← key, hm]; simp)
  refine b.ext_elem fun j => hσ ?_
  simpa using congrFun h1 j

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis A M`. Establish `li : LinearIndependent O fun i => r (b i)`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`. Use `choose a ha using fun i => hθ (g i)`.

Take `⟨n, hn⟩` from `hk (∑ i, a i • b i) (by simpa [map_sum, map_smulₛₗ, ha] using hg)`. Use `congrArg (fun m => θ (b.repr m i)) hn` as an intermediate fact. Simplify `this` using `[Finsupp.single_apply, apply_ite θ, ha, hξ]`. Establish `sp : ⊤ ≤ Submodule.span O (Set.range fun i => r (b i))`. Introduce `y _`.

Take `⟨m, rfl⟩` from `hr y`. Rewrite using `[← b.sum_repr m, map_sum]`. Conclude with `Submodule.sum_mem _ fun i _ => by`. Rewrite using `[map_smulₛₗ]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Set `c` to `Module.Basis.mk li sp`. Conclude with `⟨Module.Free.of_basis c, Module.Finite.of_basis c, by`. Rewrite using `[Module.finrank_eq_card_basis c, Module.finrank_eq_card_chooseBasisIndex]⟩`.
-/
theorem free_of_reduction [Nontrivial A] [Nontrivial O] [Module.Free A M] [Module.Finite A M]
    {θ : A →+* O} (hθ : Surjective θ) {ξ : A} (hξ : θ ξ = 0) (r : M →ₛₗ[θ] D) (hr : Surjective r)
    (hk : ∀ m, r m = 0 → ∃ n, m = ξ • n) :
    Module.Free O D ∧ Module.Finite O D ∧ Module.finrank O D = Module.finrank A M := by
  classical
  let b := Module.Free.chooseBasis A M
  have li : LinearIndependent O fun i => r (b i) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose a ha using fun i => hθ (g i)
    obtain ⟨n, hn⟩ := hk (∑ i, a i • b i) (by simpa [map_sum, map_smulₛₗ, ha] using hg)
    have := congrArg (fun m => θ (b.repr m i)) hn
    simpa [Finsupp.single_apply, apply_ite θ, ha, hξ] using this
  have sp : ⊤ ≤ Submodule.span O (Set.range fun i => r (b i)) := by
    intro y _
    obtain ⟨m, rfl⟩ := hr y
    rw [← b.sum_repr m, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let c := Module.Basis.mk li sp
  exact ⟨Module.Free.of_basis c, Module.Finite.of_basis c, by
    rw [Module.finrank_eq_card_basis c, Module.finrank_eq_card_chooseBasisIndex]⟩

/- English proof (translation)
Use `haveI : Module.Finite O (Module.Dual O Y) := Module.Finite.of_surjective π hπ`. Use `haveI : Module.Flat O (Module.Dual O Y) := by`. Rewrite using `[Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]`. Introduce and unpack `y ⟨⟨a, ha⟩, hy⟩`. Use `LinearMap.ext fun w => ?_` and prove the remaining obligations.

Conclude with `(mul_eq_zero.1 (LinearMap.congr_fun hy w)).resolve_left (nonZeroDivisors.ne_zero ha)`. Use `haveI : Module.Free O (Module.Dual O Y) := Module.free_of_flat_of_isLocalRing`. Take `⟨s, hs⟩` from `Module.projective_lifting_property π LinearMap.id hπ`. Establish `hs' : ∃ l, π ∘ₗ l = LinearMap.id` using `⟨s, hs⟩`. Take `⟨t, ht⟩ : ∃ l, l ∘ₗ ι = LinearMap.id` from `((he.split_tfae hι hπ).out 0 1).1 hs'`.

Use `haveI : Module.Finite O X := Module.Finite.of_surjective t fun x => ⟨ι x, LinearMap.congr_fun ht x⟩`. Use `haveI : Module.Projective O X := Module.Projective.of_split ι t ht`. Conclude with `⟨⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩, inferInstance, inferInstance⟩`.
-/
theorem free_of_exact [IsDomain O] [ValuationRing O] [Module.Free O D] [Module.Finite O D]
    {X Y : Type*} [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module O Y]
    (ι : X →ₗ[O] D) (π : D →ₗ[O] Module.Dual O Y) (hι : Injective ι) (he : Function.Exact ι π)
    (hπ : Surjective π) :
    (Module.Free O X ∧ Module.Finite O X) ∧
      (Module.Free O (Module.Dual O Y) ∧ Module.Finite O (Module.Dual O Y)) := by
  haveI : Module.Finite O (Module.Dual O Y) := Module.Finite.of_surjective π hπ
  haveI : Module.Flat O (Module.Dual O Y) := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro y ⟨⟨a, ha⟩, hy⟩
    refine LinearMap.ext fun w => ?_
    exact (mul_eq_zero.1 (LinearMap.congr_fun hy w)).resolve_left (nonZeroDivisors.ne_zero ha)
  haveI : Module.Free O (Module.Dual O Y) := Module.free_of_flat_of_isLocalRing
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hs' : ∃ l, π ∘ₗ l = LinearMap.id := ⟨s, hs⟩
  obtain ⟨t, ht⟩ : ∃ l, l ∘ₗ ι = LinearMap.id := ((he.split_tfae hι hπ).out 0 1).1 hs'
  haveI : Module.Finite O X := Module.Finite.of_surjective t fun x => ⟨ι x, LinearMap.congr_fun ht x⟩
  haveI : Module.Projective O X := Module.Projective.of_split ι t ht
  exact ⟨⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩, inferInstance, inferInstance⟩

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Use `IsHausdorff.haus' (I := span {(p : A)}) _ fun n => ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `PDiv.pow_dvd_sub_digit n a`. Establish `h` using `sub_eq_iff_eq_add.1 hc`. Establish `h1 : T (a • f) - φ a • T f = (p : A) ^ n • (T (c • f) - φ c • T f)` using `by conv_lhs => rw [h]`.

Rewrite using `[add_smul, map_add, map_add, add_smul, Nat.cast_smul_eq_nsmul, map_nsmul, map_natCast, Nat.cast_smul_eq_nsmul, mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, map_nsmul, map_mul, map_natCast, mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, smul_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[SModEq.zero, h1, Ideal.span_singleton_pow]`. Conclude with `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top`.
-/
theorem map_padic_smul {p : ℕ} [Fact p.Prime] [IsHausdorff (span {(p : A)}) M] {N : Type*}
    [AddCommGroup N] [Module ℤ_[p] N] (φ : ℤ_[p] →+* A) (T : N →+ M) (a : ℤ_[p]) (f : N) :
    T (a • f) = φ a • T f := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := span {(p : A)}) _ fun n => ?_
  obtain ⟨c, hc⟩ := PDiv.pow_dvd_sub_digit n a
  have h := sub_eq_iff_eq_add.1 hc
  have h1 : T (a • f) - φ a • T f = (p : A) ^ n • (T (c • f) - φ c • T f) := by
    conv_lhs => rw [h]
    rw [add_smul, map_add, map_add, add_smul, Nat.cast_smul_eq_nsmul, map_nsmul, map_natCast,
      Nat.cast_smul_eq_nsmul, mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, map_nsmul, map_mul,
      map_natCast, mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul,
      smul_sub]
    abel
  rw [SModEq.zero, h1, Ideal.span_singleton_pow]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

end Linear

section Tilt

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[coeff_frobenius_charP, phiInv, map_coeff]`. Conclude with `frobeniusEquiv_symm_pow_p _ p _`.
-/
theorem frobenius_phiInv (a : Ainf p O) : WittVector.frobenius (phiInv p O a) = a := by
  ext n
  rw [coeff_frobenius_charP, phiInv, map_coeff]
  exact frobeniusEquiv_symm_pow_p _ p _

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[phiInv, map_coeff, coeff_frobenius_charP]`. Conclude with `(_root_.frobeniusEquiv (PreTilt O p) p).symm_apply_apply _`.
-/
theorem phiInv_frobenius (a : Ainf p O) : phiInv p O (WittVector.frobenius a) = a := by
  ext n
  rw [phiInv, map_coeff, coeff_frobenius_charP]
  exact (_root_.frobeniusEquiv (PreTilt O p) p).symm_apply_apply _

/- English proof (translation)
The claim follows from `LeftInverse.injective phiInv_frobenius`.
-/
theorem frobenius_injective : Injective (WittVector.frobenius : Ainf p O →+* Ainf p O) :=
  LeftInverse.injective phiInv_frobenius

/- English proof (translation)
Use `conv_lhs => rw [← xi_mul_nu, map_mul, ← phiInv_mu, frobenius_phiInv]`.
-/
theorem frobenius_mu (ε : PreTilt O p) : WittVector.frobenius (Sandwich.mu ε) =
    WittVector.frobenius (xi ε) * Sandwich.mu ε := by
  conv_lhs => rw [← xi_mul_nu, map_mul, ← phiInv_mu, frobenius_phiInv]

/- English proof (translation)
Rewrite using `[← map_pow, iterate_succ_apply']`. Use `congr 1`. Conclude with `(_root_.frobeniusEquiv (PreTilt O p) p).apply_symm_apply _`.
-/
theorem untilt_root_succ_pow (ε : PreTilt O p) (n : ℕ) :
    (root^[n + 1] ε).untilt ^ p = (root^[n] ε).untilt := by
  rw [← map_pow, iterate_succ_apply']
  congr 1
  exact (_root_.frobeniusEquiv (PreTilt O p) p).apply_symm_apply _

/- English proof (translation)
The claim follows from `(untilt_root_succ_pow ε 0).symm.trans hε.pow_eq_one`.
-/
theorem untilt_root_zero {ε : PreTilt O p} (hε : IsPrimitiveRoot (root ε).untilt p) :
    (root^[0] ε).untilt = 1 :=
  (untilt_root_succ_pow ε 0).symm.trans hε.pow_eq_one

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero => rw [untilt_root_zero hε, pow_zero]`. Conclude with `IsPrimitiveRoot.one`. Consider the case `succ n`. Establish `h1 : ∀ k, (root^[k + 1] ε).untilt ^ p ^ k = (root ε).untilt` using `fun k => by`.

Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ', pow_mul, untilt_root_succ_pow, ih]`. Establish `h2` using `orderOf_eq_prime_pow (p := p) (n := n) (x := (root^[n + 1] ε).untilt) (by rw [h1]; exact hε.ne_one (Fact.out : p.Prime).one_lt) (by rw [pow_succ, pow_mul, h1, hε.pow_eq_one])`. Rewrite using `[← h2]`.

Conclude with `IsPrimitiveRoot.orderOf _`.
-/
theorem isPrimitiveRoot_untilt_root {ε : PreTilt O p} (hε : IsPrimitiveRoot (root ε).untilt p)
    (n : ℕ) : IsPrimitiveRoot (root^[n] ε).untilt (p ^ n) := by
  cases n with
  | zero => rw [untilt_root_zero hε, pow_zero]; exact IsPrimitiveRoot.one
  | succ n =>
    have h1 : ∀ k, (root^[k + 1] ε).untilt ^ p ^ k = (root ε).untilt := fun k => by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ', pow_mul, untilt_root_succ_pow, ih]
    have h2 := orderOf_eq_prime_pow (p := p) (n := n) (x := (root^[n + 1] ε).untilt)
      (by rw [h1]; exact hε.ne_one (Fact.out : p.Prime).one_lt)
      (by rw [pow_succ, pow_mul, h1, hε.pow_eq_one])
    rw [← h2]
    exact IsPrimitiveRoot.orderOf _

/- English proof (translation)
Introduce and unpack `⟨c, hc⟩`. Establish `h` using `congrArg (WittVector.constantCoeff (p := p)) hc`. Rewrite `h` using `[map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, Sandwich.mu, map_sub, map_one, constantCoeff_apply, teichmuller_coeff_zero, sub_eq_zero]`. Use `hε.ne_one (Fact.out : p.Prime).one_lt ?_` and prove the remaining obligations. Rewrite using `[h, root, map_one, map_one]`.
-/
theorem not_dvd_mu {ε : PreTilt O p} (hε : IsPrimitiveRoot (root ε).untilt p) :
    ¬ (p : Ainf p O) ∣ Sandwich.mu ε := by
  rintro ⟨c, hc⟩
  have h := congrArg (WittVector.constantCoeff (p := p)) hc
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, Sandwich.mu, map_sub, map_one,
    constantCoeff_apply, teichmuller_coeff_zero, sub_eq_zero] at h
  refine hε.ne_one (Fact.out : p.Prime).one_lt ?_
  rw [h, root, map_one, map_one]

end Tilt

end Dieudonne

open Dieudonne

section Main

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]

variable (p O) in

def PDivGroup.dualFunctor : PDivGroup p O ⥤ (PDivGroup p O)ᵒᵖ where
  obj G := op G.dual
  map f := (dualHom _ _ f).op
  map_id _ := rfl
  map_comp _ _ := rfl

instance PDivGroup.dualFunctor_additive : (dualFunctor p O).Additive where
  map_add {G H f g} := congrArg Quiver.Hom.op (map_add (dualHom G H) f g)

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

/- English proof (translation)
Take `⟨M, D, φ, r, ι, π, hadd, hM, hφ, nφ, hr, nr, hex, nι, nπ, ⟨ec, hec⟩, ⟨em, hem⟩, hff⟩` from `h`. Use `haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)`. Use `haveI : ValuationRing O := ValuationRing.of_integers v hv`. Use `haveI : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p`. Use `haveI : IsAdicComplete (span {(p : Ainf p O)}) (Ainf p O) := WittVector.isAdicCompleteIdealSpanP`.

Establish `hξ : xi ε ≠ 0` using `fun h0 => one_ne_zero (ReciprocityTheory.PGsh.Ainf.xi_nzd p O hv ε hε 1 ((one_mul _).trans h0))`. Establish `hξ' : (WittVector.frobenius (xi ε) : Ainf p O) ≠ 0` using `fun h0 => hξ (frobenius_injective (h0.trans (map_zero _).symm))`. Establish `inj : ∀ G, Injective (φ G)` using `fun G => by haveI := (hM G).1 haveI := (hM G).2.1`. Conclude with `injective_of_smul_mem_range frobenius_injective (φ G) hξ' (hφ G)`. Use `choose s hs using hφ`.

Set `ψ : ∀ G : PDivGroup p O, M.obj (op G) →ₛₗ[phiInv p O] M.obj (op G)` to `fun G => { toFun := s G map_add' := fun a b => inj G (by rw [map_add, hs, hs, hs, smul_add]) map_smul' := fun a m => inj G (by rw [map_smulₛₗ, hs, hs, frobenius_phiInv, smul_comm]) }`. Establish `hψ : ∀ G m, φ G (ψ G m) = (WittVector.frobenius (xi ε) : Ainf p O) • m` using `hs`. Establish `nψ : ∀ (G H : PDivGroup p O) (f : G ⟶ H) (m : M.obj (op H)), M.map f.op (ψ H m) = ψ G (M.map f.op m)` using `fun G H f m => inj G (by rw [← nφ, hψ, hψ, map_smul])`. Establish `h0` using `untilt_root_zero hε`. Set `t` to `muTate O (fun n => (root^[n] ε).untilt) h0 (untilt_root_succ_pow ε)`.

Set `T : (const p O ⟶ PDivGroup.mu p O) →+ Ainf p O` to `AddMonoidHom.mk' (fun f => ec (M.map f.op (em.symm 1))) fun f g => by`. Rewrite using `[op_add, M.map_add, ← map_add]`. Both sides reduce to the same expression. Set `g : M.obj (op (PDivGroup.mu p O)) →ₗ[Ainf p O] M.obj (op (const p O))` to `ec.symm.toLinearMap ∘ₗ (Sandwich.mu ε • em.toLinearMap)`. Take `⟨f, hf, -⟩` from `hff g fun m => ec.injective (by`.

Simplify using `only [g, hec, LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, smul_eq_mul, hem, map_mul, frobenius_mu]`. Use the proof step `ring)`. Take `⟨t', rfl⟩` from `(dualChar (PDivGroup.mu p O)).surjective f`. Take `⟨a, rfl⟩` from `(smul_muTate_bijective (O := O) _ h0 (untilt_root_succ_pow ε) (isPrimitiveRoot_untilt_root hε)).2 t'`. Establish `ha : ofPadic p O a * T (dualChar _ t) = Sandwich.mu ε`.

Rewrite using `[← smul_eq_mul, ← map_padic_smul, ← map_smul]`. Use `congrArg (fun l => ec (l (em.symm 1))) hf` as an intermediate fact. Conclude with `this.trans (by simp [g])`. Establish `hu : IsUnit a`. Assume the negation of the conclusion as `hu`.

Take `⟨c, rfl⟩ : (p : ℤ_[p]) ∣ a` from `(PadicInt.norm_lt_one_iff_dvd a).1 (PadicInt.not_isUnit_iff.1 hu)`. Conclude with `not_dvd_mu hε ⟨_, by rw [← ha, map_mul, map_natCast, mul_assoc]⟩`. Take `⟨u, rfl⟩` from `hu`. Establish `hT : ∀ m, ec (M.map (dualChar _ t).op m) = ofPadic p O ↑u⁻¹ * Sandwich.mu ε * em m`. Introduce `m`.

Establish `hm : m = em m • em.symm 1` using `em.injective (by simp)`. Rewrite using `[← ha, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul, mul_comm]`. Use `conv_lhs => rw [hm, map_smul, map_smul]`. Both sides reduce to the same expression. Set `b` to `(M.mapIso (PDivGroup.mu p O).bidual.op).toLinearEquiv`.

Establish `hπ : ∀ G : PDivGroup p O, Bijective (lieMap G.dual.dual G G.bidual.inv)` using `fun G => bijective_iff_has_inverse.2 ⟨lieMap _ _ G.bidual.hom, fun x => by rw [← LinearMap.comp_apply, ← lieMap_comp, Iso.inv_hom_id, lieMap_id]; rfl, fun x => by rw [← LinearMap.comp_apply, ← lieMap_comp, Iso.hom_inv_id, lieMap_id]; rfl⟩`. Establish `hex' : ∀ G : PDivGroup p O, Injective (ι G.dual) ∧ Function.Exact (ι G.dual) (lieMap G.dual.dual G G.bidual.inv ∘ₗ π G.dual) ∧ Surjective (lieMap G.dual.dual G G.bidual.inv ∘ₗ π G.dual)` using `fun G => ⟨(hex _).1, fun x => by`. Rewrite using `[← (hex G.dual).2.1 x, LinearMap.comp_apply, map_eq_zero_iff _ (hπ G).1],`. Use the proof step `(hπ G).2.comp (hex _).2.2⟩`. Establish `k1 : ∀ G : PDivGroup p O, Injective (ψ G) ∧ ∀ m, ∃ n, ψ G n = xi ε • m` using `fun G => by haveI := (hM G).1`.

Use `⟨fun x y hxy => ?_, fun m => ⟨φ G m, inj _ ?_⟩⟩` and prove the remaining obligations. Use `congrArg (φ G) hxy` as an intermediate fact. Rewrite `this` using `[hψ, hψ]`. Conclude with `smul_right_injective _ hξ' this`. Conclude with `(hψ _ _).trans (map_smulₛₗ (φ G) _ _).symm`.

Establish `k2 : ∀ (G G' : PDivGroup p O) (f : G ⟶ G') (x : D.obj (op G.dual)), lieMap _ _ G'.bidual.inv (π G'.dual (D.map (dualHom G G' f).op x)) = lieMap G G' f (lieMap _ _ G.bidual.inv (π G.dual x))` using `fun G G' f x => by`. Rewrite using `[nπ, ← LinearMap.comp_apply, ← lieMap_comp, dualHom_dualHom_bidual_inv, lieMap_comp]`. Both sides reduce to the same expression. Establish `k3 : ∀ m : M.obj (op (PDivGroup.mu p O).dual.dual), em (M.map (PDivGroup.mu p O).bidual.hom.op (ψ _ m)) = phiInv p O (em (M.map (PDivGroup.mu p O).bidual.hom.op m))` using `fun m => by`. Rewrite using `[nψ]`.

Use `frobenius_injective (mul_left_cancel₀ hξ' ?_)` and prove the remaining obligations. Rewrite using `[← hem, hψ, map_smul, frobenius_phiInv, smul_eq_mul]`. Establish `k4 : ∀ m, ec (ψ _ m) = xi ε * phiInv p O (ec m)` using `fun m => by`. Use `frobenius_injective ?_` and prove the remaining obligations. Rewrite using `[← hec, hψ, map_smul, map_mul, frobenius_phiInv, smul_eq_mul]`.

Establish `k5 : ∀ m : M.obj (op (PDivGroup.mu p O).dual.dual), ec (M.map (dualHom _ _ (constHom _ t)).op m) = ofPadic p O ↑u⁻¹ * Sandwich.mu ε * em (M.map (PDivGroup.mu p O).bidual.hom.op m)` using `fun m => by`. Rewrite using `[← hT, ← dualHom_constHom, ← ModuleCat.comp_apply, ← M.map_comp, ← op_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]`. Use `⟨dualFunctor p O ⋙ M, dualFunctor p O ⋙ D, fun G => ψ G.dual, fun G => r G.dual, fun G => ι G.dual, fun G => lieMap G.dual.dual G G.bidual.inv ∘ₗ π G.dual, inferInstance, fun G => hM G.dual, fun G => k1 G.dual, fun G G' f => nψ _ _ (dualHom G G' f), fun G => hr G.dual, fun G G' f …` and prove the remaining obligations. Use `haveI := (hM G.dual).1 haveI := (hM G.dual).2.1`. Take `⟨h1, h2, h3⟩` from `free_of_reduction (ReciprocityTheory.PGsh.Ainf.theta_surj p O hv) (ReciprocityTheory.PGsh.Ainf.theta_xi p O hv ε hε) (r G.dual) (hr _).1 fun m => ((hr _).2 m).1`.

Conclude with `⟨⟨h1, h2, h3.trans (hM G.dual).2.2⟩, free_of_exact _ _ (hex' G).1 (hex' G).2.1 (hex' G).2.2⟩`. Take `rfl : ζ = fun n => (root^[n] ε).untilt` from `funext hζ`. Conclude with `k5 m`.
-/
theorem Published.PrismaticDieudonneHodgeAt.covariant {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} [Algebra O C] (hv : v.Integers O) {ε : PreTilt O p}
    (hε : IsPrimitiveRoot (root ε).untilt p) (h : Published.PrismaticDieudonneHodgeAt ε) :
    CovariantDieudonneAt ε := by
  obtain ⟨M, D, φ, r, ι, π, hadd, hM, hφ, nφ, hr, nr, hex, nι, nπ, ⟨ec, hec⟩, ⟨em, hem⟩, hff⟩ := h
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  haveI : IsAdicComplete (span {(p : Ainf p O)}) (Ainf p O) := WittVector.isAdicCompleteIdealSpanP
  have hξ : xi ε ≠ 0 := fun h0 =>
    one_ne_zero (ReciprocityTheory.PGsh.Ainf.xi_nzd p O hv ε hε 1 ((one_mul _).trans h0))
  have hξ' : (WittVector.frobenius (xi ε) : Ainf p O) ≠ 0 := fun h0 =>
    hξ (frobenius_injective (h0.trans (map_zero _).symm))
  have inj : ∀ G, Injective (φ G) := fun G => by
    haveI := (hM G).1
    haveI := (hM G).2.1
    exact injective_of_smul_mem_range frobenius_injective (φ G) hξ' (hφ G)
  choose s hs using hφ
  let ψ : ∀ G : PDivGroup p O, M.obj (op G) →ₛₗ[phiInv p O] M.obj (op G) := fun G =>
    { toFun := s G
      map_add' := fun a b => inj G (by rw [map_add, hs, hs, hs, smul_add])
      map_smul' := fun a m => inj G (by rw [map_smulₛₗ, hs, hs, frobenius_phiInv, smul_comm]) }
  have hψ : ∀ G m, φ G (ψ G m) = (WittVector.frobenius (xi ε) : Ainf p O) • m := hs
  have nψ : ∀ (G H : PDivGroup p O) (f : G ⟶ H) (m : M.obj (op H)),
      M.map f.op (ψ H m) = ψ G (M.map f.op m) := fun G H f m =>
    inj G (by rw [← nφ, hψ, hψ, map_smul])

  have h0 := untilt_root_zero hε
  let t := muTate O (fun n => (root^[n] ε).untilt) h0 (untilt_root_succ_pow ε)
  let T : (const p O ⟶ PDivGroup.mu p O) →+ Ainf p O :=
    AddMonoidHom.mk' (fun f => ec (M.map f.op (em.symm 1))) fun f g => by
      rw [op_add, M.map_add, ← map_add]; rfl
  let g : M.obj (op (PDivGroup.mu p O)) →ₗ[Ainf p O] M.obj (op (const p O)) :=
    ec.symm.toLinearMap ∘ₗ (Sandwich.mu ε • em.toLinearMap)
  obtain ⟨f, hf, -⟩ := hff g fun m => ec.injective (by
    simp only [g, hec, LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, smul_eq_mul, hem, map_mul, frobenius_mu]
    ring)
  obtain ⟨t', rfl⟩ := (dualChar (PDivGroup.mu p O)).surjective f
  obtain ⟨a, rfl⟩ := (smul_muTate_bijective (O := O) _ h0 (untilt_root_succ_pow ε)
    (isPrimitiveRoot_untilt_root hε)).2 t'
  have ha : ofPadic p O a * T (dualChar _ t) = Sandwich.mu ε := by
    rw [← smul_eq_mul, ← map_padic_smul, ← map_smul]
    have := congrArg (fun l => ec (l (em.symm 1))) hf
    exact this.trans (by simp [g])
  have hu : IsUnit a := by
    by_contra hu
    obtain ⟨c, rfl⟩ : (p : ℤ_[p]) ∣ a := (PadicInt.norm_lt_one_iff_dvd a).1
      (PadicInt.not_isUnit_iff.1 hu)
    exact not_dvd_mu hε ⟨_, by rw [← ha, map_mul, map_natCast, mul_assoc]⟩
  obtain ⟨u, rfl⟩ := hu
  have hT : ∀ m, ec (M.map (dualChar _ t).op m) = ofPadic p O ↑u⁻¹ * Sandwich.mu ε * em m := by
    intro m
    have hm : m = em m • em.symm 1 := em.injective (by simp)
    rw [← ha, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul, mul_comm]
    conv_lhs => rw [hm, map_smul, map_smul]
    rfl
  let b := (M.mapIso (PDivGroup.mu p O).bidual.op).toLinearEquiv
  have hπ : ∀ G : PDivGroup p O, Bijective (lieMap G.dual.dual G G.bidual.inv) := fun G =>
    bijective_iff_has_inverse.2 ⟨lieMap _ _ G.bidual.hom,
      fun x => by rw [← LinearMap.comp_apply, ← lieMap_comp, Iso.inv_hom_id, lieMap_id]; rfl,
      fun x => by rw [← LinearMap.comp_apply, ← lieMap_comp, Iso.hom_inv_id, lieMap_id]; rfl⟩
  have hex' : ∀ G : PDivGroup p O, Injective (ι G.dual) ∧
      Function.Exact (ι G.dual) (lieMap G.dual.dual G G.bidual.inv ∘ₗ π G.dual) ∧
      Surjective (lieMap G.dual.dual G G.bidual.inv ∘ₗ π G.dual) := fun G =>
    ⟨(hex _).1, fun x => by
      rw [← (hex G.dual).2.1 x, LinearMap.comp_apply, map_eq_zero_iff _ (hπ G).1],
      (hπ G).2.comp (hex _).2.2⟩
  have k1 : ∀ G : PDivGroup p O, Injective (ψ G) ∧ ∀ m, ∃ n, ψ G n = xi ε • m := fun G => by
    haveI := (hM G).1
    refine ⟨fun x y hxy => ?_, fun m => ⟨φ G m, inj _ ?_⟩⟩
    · have := congrArg (φ G) hxy
      rw [hψ, hψ] at this
      exact smul_right_injective _ hξ' this
    · exact (hψ _ _).trans (map_smulₛₗ (φ G) _ _).symm
  have k2 : ∀ (G G' : PDivGroup p O) (f : G ⟶ G') (x : D.obj (op G.dual)),
      lieMap _ _ G'.bidual.inv (π G'.dual (D.map (dualHom G G' f).op x)) =
        lieMap G G' f (lieMap _ _ G.bidual.inv (π G.dual x)) := fun G G' f x => by
    rw [nπ, ← LinearMap.comp_apply, ← lieMap_comp, dualHom_dualHom_bidual_inv, lieMap_comp]
    rfl
  have k3 : ∀ m : M.obj (op (PDivGroup.mu p O).dual.dual),
      em (M.map (PDivGroup.mu p O).bidual.hom.op (ψ _ m)) =
        phiInv p O (em (M.map (PDivGroup.mu p O).bidual.hom.op m)) := fun m => by
    rw [nψ]
    refine frobenius_injective (mul_left_cancel₀ hξ' ?_)
    rw [← hem, hψ, map_smul, frobenius_phiInv, smul_eq_mul]
  have k4 : ∀ m, ec (ψ _ m) = xi ε * phiInv p O (ec m) := fun m => by
    refine frobenius_injective ?_
    rw [← hec, hψ, map_smul, map_mul, frobenius_phiInv, smul_eq_mul]
  have k5 : ∀ m : M.obj (op (PDivGroup.mu p O).dual.dual),
      ec (M.map (dualHom _ _ (constHom _ t)).op m) = ofPadic p O ↑u⁻¹ * Sandwich.mu ε *
        em (M.map (PDivGroup.mu p O).bidual.hom.op m) := fun m => by
    rw [← hT, ← dualHom_constHom, ← ModuleCat.comp_apply, ← M.map_comp, ← op_comp, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  refine ⟨dualFunctor p O ⋙ M, dualFunctor p O ⋙ D, fun G => ψ G.dual, fun G => r G.dual,
    fun G => ι G.dual, fun G => lieMap G.dual.dual G G.bidual.inv ∘ₗ π G.dual, inferInstance,
    fun G => hM G.dual, fun G => k1 G.dual,
    fun G G' f => nψ _ _ (dualHom G G' f), fun G => hr G.dual,
    fun G G' f => nr _ _ (dualHom G G' f), hex', fun G G' f => nι _ _ (dualHom G G' f),
    k2, fun G => ?_, b ≪≫ₗ em, ec, u⁻¹, k3, k4, fun ζ h0' h' hζ m => ?_⟩
  · haveI := (hM G.dual).1
    haveI := (hM G.dual).2.1
    obtain ⟨h1, h2, h3⟩ := free_of_reduction (ReciprocityTheory.PGsh.Ainf.theta_surj p O hv)
      (ReciprocityTheory.PGsh.Ainf.theta_xi p O hv ε hε) (r G.dual) (hr _).1 fun m => ((hr _).2 m).1
    exact ⟨⟨h1, h2, h3.trans (hM G.dual).2.2⟩,
      free_of_exact _ _ (hex' G).1 (hex' G).2.1 (hex' G).2.2⟩
  · obtain rfl : ζ = fun n => (root^[n] ε).untilt := funext hζ
    exact k5 m

end Main

/- English proof (translation)
The claim follows from `(h p C v O hv ε hε).covariant hv hε`.
-/
theorem Published.PrismaticDieudonneHodge.covariant (h : Published.PrismaticDieudonneHodge) (p : ℕ) [Fact p.Prime]
    (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type)
    [CommRing O] [Algebra O C] (hv : v.Integers O) [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (span {(p : O)}) O] (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (root ε).untilt p) : CovariantDieudonneAt ε :=
  (h p C v O hv ε hε).covariant hv hε

/- English proof (translation)
Take `⟨h1, h2, ε, hv, hε⟩` from `PadicComplexHost.main p`. Conclude with `⟨h1, h2, ε, hε, h.covariant p ℂ_[p] Valued.v _ hv ε hε⟩`.
-/
example (h : Published.PrismaticDieudonneHodge) (p : ℕ) [Fact p.Prime] :
    ∃ (_ : Fact ¬IsUnit ((p : ℕ) : 𝓞_ℂ_[p]))
      (_ : IsAdicComplete (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p]) (ε : PreTilt 𝓞_ℂ_[p] p),
      IsPrimitiveRoot (root ε).untilt p ∧ CovariantDieudonneAt ε := by
  obtain ⟨h1, h2, ε, hv, hε⟩ := PadicComplexHost.main p
  exact ⟨h1, h2, ε, hε, h.covariant p ℂ_[p] Valued.v _ hv ε hε⟩

end GlobalTheory
