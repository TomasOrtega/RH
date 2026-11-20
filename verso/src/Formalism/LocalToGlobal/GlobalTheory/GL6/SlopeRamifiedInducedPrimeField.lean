import Formalism.LocalToGlobal.Columns.SliceIntegralDeltaNeBot
import Formalism.LocalToGlobal.GlobalTheory.GL6.RamifiedLatticePropsOfModel
import Formalism.LocalToGlobal.GlobalTheory.GL6.RamifiedLatticeOfRankSlopeLength

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.HN Formalism.HermitianLatticesTheory Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Col NumberField Module

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  {ι : Type} [Fintype ι] [DecidableEq ι] (G : ι → Type) [∀ i, CommGroup (G i)] [∀ i, Fintype (G i)]
  [∀ i, DecidableEq (G i)]

/- English proof (translation)
Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, hmaj]`. Simplify using `only [T2.kronMap_apply]`. Establish `hs` using `fun a : α => T2.sesq_sum_zsmul (isSesq_maj Wh.b Wh.X) v (fun b => t b a) F (fun c => t c a) F'`. Simplify using `only [hs]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_mul, Matrix.mul_apply]`. Use `push_cast`.

Both sides reduce to the same expression.
-/
theorem majorant_kronecker_map (B Wh : HLat K) {α β : Type} [Fintype α] [Fintype β]
    (Ψ : (α → Wh.V) →ₗ[K] B.V)
    (hmaj : ∀ v F F', majAt B.b B.X v (Ψ F) (Ψ F') = ∑ a, majAt Wh.b Wh.X v (F a) (F' a))
    (t : Matrix β α ℤ) (v : InfinitePlace K) (F F' : β → Wh.V) :
    majAt B.b B.X v ((Ψ ∘ₗ T2.kronMap K Wh.V t) F) ((Ψ ∘ₗ T2.kronMap K Wh.V t) F') =
      ∑ b, ∑ c, (((t * t.transpose) b c : ℤ) : ℂ) * majAt Wh.b Wh.X v (F b) (F' c) := by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hmaj]
  simp only [T2.kronMap_apply]
  have hs := fun a : α => T2.sesq_sum_zsmul (isSesq_maj Wh.b Wh.X) v (fun b => t b a) F (fun c => t c a) F'
  simp only [hs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_mul, Matrix.mul_apply]
  push_cast
  rfl

/- English proof (translation)
Establish `e` using `T2.kron_mu B Wh hB hW hW0 (Ψ ∘ₗ T2.kronMap K Wh.V (1 : Matrix α α ℤ)) (by rw [T2.kronMap_one]; exact hΨ) (1 * (1 : Matrix α α ℤ).transpose) (by simp) (majorant_kronecker_map B Wh Ψ hmaj 1)`. Rewrite `e` using `[T2.kronMap_one, LinearMap.comp_id, ← hL]`. Simplify using `using e`.
-/
theorem slope_eq_of_isometric_sum (B Wh : HLat K) (hB : FrameOK B) (hW : Wh.Good) (hW0 : Wh.L ≠ ⊥)
    {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    (Ψ : (α → Wh.V) →ₗ[K] B.V) (hΨ : Function.Injective Ψ)
    (hmaj : ∀ v F F', majAt B.b B.X v (Ψ F) (Ψ F') = ∑ a, majAt Wh.b Wh.X v (F a) (F' a))
    (hL : B.L = (T2.piL α Wh.L).map (Ψ.restrictScalars (𝓞 K))) :
    B.mu = Wh.mu := by
  have e := T2.kron_mu B Wh hB hW hW0 (Ψ ∘ₗ T2.kronMap K Wh.V (1 : Matrix α α ℤ))
    (by rw [T2.kronMap_one]; exact hΨ) (1 * (1 : Matrix α α ℤ).transpose) (by simp)
    (majorant_kronecker_map B Wh Ψ hmaj 1)
  rw [T2.kronMap_one, LinearMap.comp_id, ← hL] at e
  simpa using e

/- English proof (translation)
Use `haveI : FiniteDimensional K Wh.V := Module.Finite.of_basis Wh.b`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨F, hF, rfl⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hL]`. Use `⟨T2.kronMap K Wh.V (T2.szVec G) F, fun a _ => ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[T2.kronMap_apply]`. Conclude with `Submodule.sum_mem _ fun c _ => zsmul_mem (hF c (Set.mem_univ c)) _`. Use `show Ψ (T2.kronMap K Wh.V (T2.szVec G) F) ∈ U`.

Rewrite using `[hU]`. Conclude with `Submodule.mem_map_of_mem (T2.kron_szVec_mem G F)`. Introduce and unpack `⟨hx, hxU⟩`. Rewrite `hx` using `[hL]`. Take `⟨F0, hF0, rfl⟩` from `hx`.

Establish `hxU' : Ψ F0 ∈ U` using `hxU`. Rewrite `hxU'` using `[hU]`. Take `⟨F1, hF1, he⟩` from `hxU'`. Establish `h01 : F1 = F0` using `hΨ he`. Substitute `h01` using the available equality.

Rewrite `hF1` using `[← T2.range_kron_szVec]`. Take `⟨F, hF⟩` from `hF1`. Use `⟨F, fun c _ => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← T2.kron_szVec_pt (K := K) G F c, hF]`. Conclude with `hF0 _ (Set.mem_univ _)`.

Use `show Ψ (T2.kronMap K Wh.V (T2.szVec G) F) = Ψ F1`. Rewrite using `[hF]`.
-/
theorem induced_lattice_map_sz (B Wh : HLat K) (Ψ : ((∀ i, G i) → Wh.V) →ₗ[K] B.V) (hΨ : Function.Injective Ψ)
    (hL : B.L = (T2.piL (∀ i, G i) Wh.L).map (Ψ.restrictScalars (𝓞 K)))
    (U : Submodule K B.V) (hU : U = (RamFun.ramFun K G Wh.V).map Ψ) :
    (T2.piL (T2.SzIdx G) Wh.L).map ((Ψ ∘ₗ T2.kronMap K Wh.V (T2.szVec G)).restrictScalars (𝓞 K)) =
      B.L ⊓ U.restrictScalars (𝓞 K) := by
  haveI : FiniteDimensional K Wh.V := Module.Finite.of_basis Wh.b
  ext x
  constructor
  · rintro ⟨F, hF, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hL]
      refine ⟨T2.kronMap K Wh.V (T2.szVec G) F, fun a _ => ?_, rfl⟩
      rw [T2.kronMap_apply]
      exact Submodule.sum_mem _ fun c _ => zsmul_mem (hF c (Set.mem_univ c)) _
    · show Ψ (T2.kronMap K Wh.V (T2.szVec G) F) ∈ U
      rw [hU]
      exact Submodule.mem_map_of_mem (T2.kron_szVec_mem G F)
  · rintro ⟨hx, hxU⟩
    rw [hL] at hx
    obtain ⟨F0, hF0, rfl⟩ := hx
    have hxU' : Ψ F0 ∈ U := hxU
    rw [hU] at hxU'
    obtain ⟨F1, hF1, he⟩ := hxU'
    have h01 : F1 = F0 := hΨ he
    subst h01
    rw [← T2.range_kron_szVec] at hF1
    obtain ⟨F, hF⟩ := hF1
    refine ⟨F, fun c _ => ?_, ?_⟩
    · rw [← T2.kron_szVec_pt (K := K) G F c, hF]
      exact hF0 _ (Set.mem_univ _)
    · show Ψ (T2.kronMap K Wh.V (T2.szVec G) F) = Ψ F1
      rw [hF]

/- English proof (translation)
Use `T2.nonempty_SzIdx G h2` as an intermediate fact. Use `haveI : Nonempty (∀ i, G i) := ⟨1⟩`. Establish `hinj : Function.Injective (Ψ ∘ₗ T2.kronMap K Wh.V (T2.szVec G))` using `hΨ.comp (T2.kron_szVec_injective G)`. Establish `e1` using `T2.kron_mu B Wh hB hW hW0 (Ψ ∘ₗ T2.kronMap K Wh.V (T2.szVec G)) hinj (T2.szVec G * (T2.szVec G).transpose) (by rw [T2.szVec_mul_transpose]; exact T2.det_szGram_pos G) (majorant_kronecker_map B Wh Ψ hmaj (T2.szVec G))`. Rewrite `e1` using `[induced_lattice_map_sz G B Wh Ψ hΨ hL U hU, T2.szVec_mul_transpose]`.

Rewrite using `[e1, slope_eq_of_isometric_sum B Wh hB hW hW0 Ψ hΨ hmaj hL]`.
-/
theorem slope_ramified_induced (B Wh : HLat K) (hB : FrameOK B) (hW : Wh.Good) (hW0 : Wh.L ≠ ⊥)
    (Ψ : ((∀ i, G i) → Wh.V) →ₗ[K] B.V) (hΨ : Function.Injective Ψ)
    (hmaj : ∀ v F F', majAt B.b B.X v (Ψ F) (Ψ F') = ∑ a, majAt Wh.b Wh.X v (F a) (F' a))
    (hL : B.L = (T2.piL (∀ i, G i) Wh.L).map (Ψ.restrictScalars (𝓞 K)))
    (U : Submodule K B.V) (hU : U = (RamFun.ramFun K G Wh.V).map Ψ) (h2 : ∀ i, 1 < Fintype.card (G i)) :
    (withL B (B.L ⊓ U.restrictScalars (𝓞 K))).mu =
      B.mu - Real.log (((T2.szGram G).det : ℤ) : ℝ) / (Fintype.card (T2.SzIdx G) : ℝ) := by
  have := T2.nonempty_SzIdx G h2
  haveI : Nonempty (∀ i, G i) := ⟨1⟩
  have hinj : Function.Injective (Ψ ∘ₗ T2.kronMap K Wh.V (T2.szVec G)) :=
    hΨ.comp (T2.kron_szVec_injective G)
  have e1 := T2.kron_mu B Wh hB hW hW0 (Ψ ∘ₗ T2.kronMap K Wh.V (T2.szVec G)) hinj
    (T2.szVec G * (T2.szVec G).transpose) (by rw [T2.szVec_mul_transpose]; exact T2.det_szGram_pos G)
    (majorant_kronecker_map B Wh Ψ hmaj (T2.szVec G))
  rw [induced_lattice_map_sz G B Wh Ψ hΨ hL U hU, T2.szVec_mul_transpose] at e1
  rw [e1, slope_eq_of_isometric_sum B Wh hB hW hW0 Ψ hΨ hmaj hL]

/- English proof (translation)
Rewrite using `[slope_ramified_induced G B Wh hB hW hW0 Ψ hΨ hmaj hL U hU (fun i => by rw [hG i]; omega), T2.log_det_szGram_div G q hq hG]`.
-/
theorem slope_ramified_induced_prime_field (B Wh : HLat K) (hB : FrameOK B) (hW : Wh.Good) (hW0 : Wh.L ≠ ⊥)
    (Ψ : ((∀ i, G i) → Wh.V) →ₗ[K] B.V) (hΨ : Function.Injective Ψ)
    (hmaj : ∀ v F F', majAt B.b B.X v (Ψ F) (Ψ F') = ∑ a, majAt Wh.b Wh.X v (F a) (F' a))
    (hL : B.L = (T2.piL (∀ i, G i) Wh.L).map (Ψ.restrictScalars (𝓞 K)))
    (U : Submodule K B.V) (hU : U = (RamFun.ramFun K G Wh.V).map Ψ)
    (q : ℕ) (hq : 3 ≤ q) (hG : ∀ i, Fintype.card (G i) = q - 1) :
    (withL B (B.L ⊓ U.restrictScalars (𝓞 K))).mu =
      B.mu - (Fintype.card ι : ℝ) * Real.log ((q : ℝ) - 1) / ((q : ℝ) - 2) := by
  rw [slope_ramified_induced G B Wh hB hW hW0 Ψ hΨ hmaj hL U hU (fun i => by rw [hG i]; omega),
    T2.log_det_szGram_div G q hq hG]

end Generic

section Slice

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, CommGroup (G i)] [∀ i, Fintype (G i)]
  [∀ i, DecidableEq (G i)]

def t2sPsi (B : HLat K) (ρ : (∀ i, G i) →* Module.End K B.V) (W : Submodule K B.V) :
    ((∀ i, G i) → W) →ₗ[K] B.V :=
  ∑ g, (ρ g).comp (W.subtype.comp (LinearMap.proj g))

/- English proof (translation)
Simplify using `[t2sPsi, LinearMap.sum_apply]`.
-/
theorem t2sPsi_apply (B : HLat K) (ρ : (∀ i, G i) →* Module.End K B.V) (W : Submodule K B.V)
    (F : (∀ i, G i) → W) : t2sPsi B ρ W F = ∑ g, ρ g (F g : B.V) := by
  simp [t2sPsi, LinearMap.sum_apply]

def t2sNm (B : HLat K) (ρ : (∀ i, G i) →* Module.End K B.V) (i : ι) : Module.End K B.V :=
  ∑ a : G i, ρ (Pi.mulSingle i a)

/- English proof (translation)
Rewrite using `[t2sPsi_apply, t2sPsi_apply, t2sNm, LinearMap.sum_apply]`. Simplify using `only [map_sum, Submodule.coe_sum]`. Use `conv_rhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Equiv.sum_comp (Equiv.mulLeft (Pi.mulSingle i a)) (fun h => (ρ h) ((F ((Pi.mulSingle i a)⁻¹ * h) : W) : B.V))]`.

Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Simplify using `only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, Module.End.mul_apply]`.
-/
theorem norm_slice_map_sum (B : HLat K) (ρ : (∀ i, G i) →* Module.End K B.V) (W : Submodule K B.V) (i : ι)
    (F : (∀ i, G i) → W) :
    t2sNm B ρ i (t2sPsi B ρ W F) =
      t2sPsi B ρ W (fun h => ∑ a : G i, F ((Pi.mulSingle i a)⁻¹ * h)) := by
  rw [t2sPsi_apply, t2sPsi_apply, t2sNm, LinearMap.sum_apply]
  simp only [map_sum, Submodule.coe_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Equiv.sum_comp (Equiv.mulLeft (Pi.mulSingle i a))
    (fun h => (ρ h) ((F ((Pi.mulSingle i a)⁻¹ * h) : W) : B.V))]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, Module.End.mul_apply]

/- English proof (translation)
Establish `e : ∀ h, ∑ a : G i, F ((Pi.mulSingle i a)⁻¹ * h) = ∑ a : G i, F (Pi.mulSingle i a * h)`. Introduce `h`. Rewrite using `[← Equiv.sum_comp (Equiv.inv (G i))]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `[Pi.mulSingle_inv]`.

Simplify using `only [e]`.
-/
theorem sum_inv_mulSingle_zero_iff (i : ι) {M : Type} [AddCommGroup M] (F : (∀ i, G i) → M) :
    (fun h => ∑ a : G i, F ((Pi.mulSingle i a)⁻¹ * h)) = 0 ↔
      (fun h => ∑ a : G i, F (Pi.mulSingle i a * h)) = 0 := by
  have e : ∀ h, ∑ a : G i, F ((Pi.mulSingle i a)⁻¹ * h) = ∑ a : G i, F (Pi.mulSingle i a * h) := by
    intro h
    rw [← Equiv.sum_comp (Equiv.inv (G i))]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Pi.mulSingle_inv]
  simp only [e]

variable [IsTotallyComplex K]

/- English proof (translation)
Use `haveI : Module.Finite K B.V := Module.Finite.of_basis B.b`. Establish `hsub : Function.Injective W.subtype` using `Subtype.val_injective`. Take `⟨hX, hm, -⟩` from `pull_spec1 B (Module.finBasis K W) W.subtype hB.1 hsub`. Use `set Ψ := t2sPsi B ρ W with hΨ`. Establish `hL : B.L = (T2.piL (∀ i, G i) (B.L.comap (W.subtype.restrictScalars (𝓞 K)))).map (Ψ.restrictScalars (𝓞 K))`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨F, rfl⟩` from `hbij.2 x`. Conclude with `⟨F, fun g _ => (hLc F).1 hx g, rfl⟩`.

Introduce and unpack `⟨F, hF, rfl⟩`. Conclude with `(hLc F).2 fun g => hF g (Set.mem_univ g)`. Set `e` to `LinearEquiv.ofBijective Ψ hbij`. Set `π : B.V →ₗ[K] W` to `(LinearMap.proj (1 : ∀ i, G i)).comp e.symm.toLinearMap`. Establish `hπ : ∀ w : W, π (w : B.V) = w`.

Introduce `w`. Establish `h1 : Ψ (Pi.single 1 w) = (w : B.V)`. Rewrite using `[hΨ, t2sPsi_apply, Finset.sum_eq_single (1 : ∀ i, G i)]`. Simplify using the standard rewrite rules. Introduce `g _ hg`.

Simplify using `[hg]`. Simplify using the standard rewrite rules. Use `show (e.symm (w : B.V)) 1 = w`. Establish `h2 : e.symm (w : B.V) = Pi.single 1 w`. Rewrite using `[LinearEquiv.symm_apply_eq]`.

Conclude with `h1.symm`. Rewrite using `[h2]`. Simplify using the standard rewrite rules. Establish `hπL : ∀ x ∈ B.L, π x ∈ B.L.comap (W.subtype.restrictScalars (𝓞 K))`. Introduce `x hx`.

Take `⟨F, rfl⟩` from `hbij.2 x`. Establish `h3 : π (Ψ F) = F 1` using `by show (e.symm (e F)) 1 = F 1`. Rewrite using `[LinearEquiv.symm_apply_apply]`. Rewrite using `[h3]`. Conclude with `(hLc F).1 hx 1`.

Use `⟨sub B W, ⟨hX, comap_fg W.subtype hsub hB.2.1, ?_⟩, ?_, Ψ, hbij.1, ?_, hL, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce `w _`. Establish `hw : (w : B.V) ∈ Submodule.span K (B.L : Set B.V)` using `by rw [hB.2.2]; trivial`. Establish `h4` using `Submodule.mem_map_of_mem (f := π) hw`.

Rewrite `h4` using `[Submodule.map_span, hπ]`. Use `Submodule.span_mono ?_ h4` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `hπL x hx`. Introduce `h0`.

Apply `hB0` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Rewrite using `[Submodule.mem_bot]`. Take `⟨F, rfl⟩` from `hbij.2 x`.

Establish `hF : ∀ g, F g = 0`. Introduce `g`. Establish `h5 : (F g : B.V) ∈ B.L` using `(hLc F).1 hx g`. Establish `h6 : F g ∈ (sub B W).L` using `h5`. Rewrite `h6` using `[h0, Submodule.mem_bot]`.

Conclude with `h6`. Rewrite using `[t2sPsi_apply]`. Simplify using `[hF]`. Introduce `v F F'`. Rewrite using `[hΨ, t2sPsi_apply, t2sPsi_apply]`.

Establish `hs` using `T2.sesq_sum_zsmul (isSesq_maj B.b B.X) v (fun _ => (1 : ℤ)) (fun g => ρ g (F g : B.V)) (fun _ => (1 : ℤ)) (fun h => ρ h (F' h : B.V))`. Simplify using `only [one_smul, Int.cast_one, one_mul] at hs`. Rewrite using `[hs]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single g]`.

Rewrite using `[horth, if_pos rfl, hm]`. Both sides reduce to the same expression. Introduce `h _ hgh`. Rewrite using `[horth, if_neg (Ne.symm hgh)]`. Simplify using the standard rewrite rules.

Use extensionality with `x`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨F, rfl⟩` from `hbij.2 x`.

Use `⟨F, ?_, rfl⟩` and prove the remaining obligations. Simplify using `only [RamFun.ramFun, Submodule.mem_iInf, LinearMap.mem_ker]`. Introduce `i`. Establish `h7` using `hx i`. Rewrite `h7` using `[norm_slice_map_sum]`.

Establish `h8 : (fun h => ∑ a : G i, F ((Pi.mulSingle i a)⁻¹ * h)) = 0` using `hbij.1 (h7.trans (map_zero _).symm)`. Rewrite `h8` using `[sum_inv_mulSingle_zero_iff]`. Use function extensionality and compare the values at `h`. Use `congrFun h8 h` as an intermediate fact. Simplify using `only [RamFun.nmF, LinearMap.sum_apply, Finset.sum_apply, RamFun.trl_apply, Pi.zero_apply] at this ⊢`.

Conclude with `this`. Introduce and unpack `⟨F, hF, rfl⟩ i`. Simplify using `only [RamFun.ramFun, Submodule.mem_iInf, LinearMap.mem_ker] at hF`. Establish `h9` using `hF i`. Rewrite using `[norm_slice_map_sum]`.

Establish `h10 : (fun h => ∑ a : G i, F (Pi.mulSingle i a * h)) = 0`. Use function extensionality and compare the values at `h`. Use `congrFun h9 h` as an intermediate fact. Simplify using `only [RamFun.nmF, LinearMap.sum_apply, Finset.sum_apply, RamFun.trl_apply, Pi.zero_apply] at this ⊢`. Conclude with `this`.

Rewrite `h10` using `[← sum_inv_mulSingle_zero_iff]`. Use `show t2sPsi B ρ W (fun h => ∑ a : G i, F ((Pi.mulSingle i a)⁻¹ * h)) = 0`. Rewrite using `[h10, map_zero]`.
-/
theorem induced_of_slice (B : HLat K) (hB : B.Good) (hB0 : B.L ≠ ⊥)
    (ρ : (∀ i, G i) →* Module.End K B.V) (W : Submodule K B.V)
    (hbij : Function.Bijective (t2sPsi B ρ W))
    (horth : ∀ v g h (x y : W), majAt B.b B.X v (ρ g (x : B.V)) (ρ h (y : B.V)) =
      if g = h then majAt B.b B.X v (x : B.V) (y : B.V) else 0)
    (hLc : ∀ F : (∀ i, G i) → W, t2sPsi B ρ W F ∈ B.L ↔ ∀ g, (F g : B.V) ∈ B.L) :
    ∃ Wh : HLat K, Wh.Good ∧ Wh.L ≠ ⊥ ∧
      ∃ Ψ : ((∀ i, G i) → Wh.V) →ₗ[K] B.V, Function.Injective Ψ ∧
        (∀ v F F', majAt B.b B.X v (Ψ F) (Ψ F') = ∑ a, majAt Wh.b Wh.X v (F a) (F' a)) ∧
        B.L = (T2.piL (∀ i, G i) Wh.L).map (Ψ.restrictScalars (𝓞 K)) ∧
        (⨅ i, LinearMap.ker (t2sNm B ρ i)) = (RamFun.ramFun K G Wh.V).map Ψ := by
  haveI : Module.Finite K B.V := Module.Finite.of_basis B.b
  have hsub : Function.Injective W.subtype := Subtype.val_injective
  obtain ⟨hX, hm, -⟩ := pull_spec1 B (Module.finBasis K W) W.subtype hB.1 hsub
  set Ψ := t2sPsi B ρ W with hΨ

  have hL : B.L = (T2.piL (∀ i, G i) (B.L.comap (W.subtype.restrictScalars (𝓞 K)))).map
      (Ψ.restrictScalars (𝓞 K)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨F, rfl⟩ := hbij.2 x
      exact ⟨F, fun g _ => (hLc F).1 hx g, rfl⟩
    · rintro ⟨F, hF, rfl⟩
      exact (hLc F).2 fun g => hF g (Set.mem_univ g)

  let e := LinearEquiv.ofBijective Ψ hbij
  let π : B.V →ₗ[K] W := (LinearMap.proj (1 : ∀ i, G i)).comp e.symm.toLinearMap
  have hπ : ∀ w : W, π (w : B.V) = w := by
    intro w
    have h1 : Ψ (Pi.single 1 w) = (w : B.V) := by
      rw [hΨ, t2sPsi_apply, Finset.sum_eq_single (1 : ∀ i, G i)]
      · simp
      · intro g _ hg
        simp [hg]
      · simp
    show (e.symm (w : B.V)) 1 = w
    have h2 : e.symm (w : B.V) = Pi.single 1 w := by
      rw [LinearEquiv.symm_apply_eq]
      exact h1.symm
    rw [h2]
    simp
  have hπL : ∀ x ∈ B.L, π x ∈ B.L.comap (W.subtype.restrictScalars (𝓞 K)) := by
    intro x hx
    obtain ⟨F, rfl⟩ := hbij.2 x
    have h3 : π (Ψ F) = F 1 := by
      show (e.symm (e F)) 1 = F 1
      rw [LinearEquiv.symm_apply_apply]
    rw [h3]
    exact (hLc F).1 hx 1
  refine ⟨sub B W, ⟨hX, comap_fg W.subtype hsub hB.2.1, ?_⟩, ?_, Ψ, hbij.1, ?_, hL, ?_⟩
  ·
    rw [eq_top_iff]
    intro w _
    have hw : (w : B.V) ∈ Submodule.span K (B.L : Set B.V) := by rw [hB.2.2]; trivial
    have h4 := Submodule.mem_map_of_mem (f := π) hw
    rw [Submodule.map_span, hπ] at h4
    refine Submodule.span_mono ?_ h4
    rintro _ ⟨x, hx, rfl⟩
    exact hπL x hx
  ·
    intro h0
    apply hB0
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    obtain ⟨F, rfl⟩ := hbij.2 x
    have hF : ∀ g, F g = 0 := by
      intro g
      have h5 : (F g : B.V) ∈ B.L := (hLc F).1 hx g
      have h6 : F g ∈ (sub B W).L := h5
      rw [h0, Submodule.mem_bot] at h6
      exact h6
    rw [t2sPsi_apply]
    simp [hF]
  ·
    intro v F F'
    rw [hΨ, t2sPsi_apply, t2sPsi_apply]
    have hs := T2.sesq_sum_zsmul (isSesq_maj B.b B.X) v (fun _ => (1 : ℤ)) (fun g => ρ g (F g : B.V))
      (fun _ => (1 : ℤ)) (fun h => ρ h (F' h : B.V))
    simp only [one_smul, Int.cast_one, one_mul] at hs
    rw [hs]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.sum_eq_single g]
    · rw [horth, if_pos rfl, hm]
      rfl
    · intro h _ hgh
      rw [horth, if_neg (Ne.symm hgh)]
    · simp
  ·
    ext x
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, Submodule.mem_map]
    constructor
    · intro hx
      obtain ⟨F, rfl⟩ := hbij.2 x
      refine ⟨F, ?_, rfl⟩
      simp only [RamFun.ramFun, Submodule.mem_iInf, LinearMap.mem_ker]
      intro i
      have h7 := hx i
      rw [norm_slice_map_sum] at h7
      have h8 : (fun h => ∑ a : G i, F ((Pi.mulSingle i a)⁻¹ * h)) = 0 :=
        hbij.1 (h7.trans (map_zero _).symm)
      rw [sum_inv_mulSingle_zero_iff] at h8
      funext h
      have := congrFun h8 h
      simp only [RamFun.nmF, LinearMap.sum_apply, Finset.sum_apply, RamFun.trl_apply, Pi.zero_apply] at this ⊢
      exact this
    · rintro ⟨F, hF, rfl⟩ i
      simp only [RamFun.ramFun, Submodule.mem_iInf, LinearMap.mem_ker] at hF
      have h9 := hF i
      rw [norm_slice_map_sum]
      have h10 : (fun h => ∑ a : G i, F (Pi.mulSingle i a * h)) = 0 := by
        funext h
        have := congrFun h9 h
        simp only [RamFun.nmF, LinearMap.sum_apply, Finset.sum_apply, RamFun.trl_apply, Pi.zero_apply] at this ⊢
        exact this
      rw [← sum_inv_mulSingle_zero_iff] at h10
      show t2sPsi B ρ W (fun h => ∑ a : G i, F ((Pi.mulSingle i a)⁻¹ * h)) = 0
      rw [h10, map_zero]

end Slice

section AtD

variable (D : D7) (u : D.what₂.Word)

open Classical

abbrev t2sG : (D.mem u).A.vT → Type := fun v => ((D.mem u).A.Fv v)ˣ

def InducedLattice : Prop :=
  ∃ Wh : HLat D.what₂.LL, Wh.Good ∧ Wh.L ≠ ⊥ ∧
    ∃ Ψ : ((∀ v, t2sG D u v) → Wh.V) →ₗ[D.what₂.LL] ((D.fm u).lat 0).V,
      Function.Injective Ψ ∧
      (∀ v F F', majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (Ψ F) (Ψ F') =
        ∑ a, majAt Wh.b Wh.X v (F a) (F' a)) ∧
      ((D.fm u).lat 0).L = (T2.piL (∀ v, t2sG D u v) Wh.L).map (Ψ.restrictScalars (𝓞 D.what₂.LL)) ∧
      (D.fm u).ramSub = (RamFun.ramFun D.what₂.LL (t2sG D u) Wh.V).map Ψ

/- English proof (translation)
Establish `h1` using `hS.1`. Establish `hf : 0 < D.R.f` using `by show 0 < 2 * D.R.n`. Establish `: 0 < D.R.n` using `by unfold Ranks.n; positivity`. Use linear arithmetic over natural numbers and integers. Establish `hN : 0 < D.R.N D.R.m` using `D.R.N_pos _`.

Establish `: 1 ≤ D.R.f * D.R.N D.R.m` using `Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hf.ne' hN.ne')`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem three_le_level_prime (hS : Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u) : 3 ≤ (D.mem u).A.T := by
  have h1 := hS.1
  have hf : 0 < D.R.f := by
    show 0 < 2 * D.R.n
    have : 0 < D.R.n := by unfold Ranks.n; positivity
    omega
  have hN : 0 < D.R.N D.R.m := D.R.N_pos _
  have : 1 ≤ D.R.f * D.R.N D.R.m := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hf.ne' hN.ne')
  nlinarith

/- English proof (translation)
Take `⟨Wh, hW, hW0, Ψ, hΨ, hmaj, hL, hU⟩` from `h`. Establish `hB : FrameOK ((D.fm u).lat 0)` using `((D.fm u).lat_good 0).1`. Establish `hG : ∀ v, Fintype.card (t2sG D u v) = (D.mem u).A.T - 1` using `fun v => by`. Rewrite using `[Fintype.card_units, (D.mem u).A.card_Fv v]`. Establish `e` using `slope_ramified_induced_prime_field (t2sG D u) ((D.fm u).lat 0) Wh hB hW hW0 Ψ hΨ hmaj hL (D.fm u).ramSub hU (D.mem u).A.T (three_le_level_prime D u hS) hG`.

Rewrite `e` using `[(D.mem u).A.card_vT]`. Conclude with `e`.
-/
theorem slope_formula_of_induced (hS : Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u) (h : InducedLattice D u) : RamifiedSlopeFormula D u := by
  obtain ⟨Wh, hW, hW0, Ψ, hΨ, hmaj, hL, hU⟩ := h
  have hB : FrameOK ((D.fm u).lat 0) := ((D.fm u).lat_good 0).1
  have hG : ∀ v, Fintype.card (t2sG D u v) = (D.mem u).A.T - 1 := fun v => by
    rw [Fintype.card_units, (D.mem u).A.card_Fv v]
  have e := slope_ramified_induced_prime_field (t2sG D u) ((D.fm u).lat 0) Wh hB hW hW0 Ψ hΨ hmaj hL (D.fm u).ramSub hU
    (D.mem u).A.T (three_le_level_prime D u hS) hG
  rw [(D.mem u).A.card_vT] at e
  exact e

end AtD

section AtDSlice

variable (D : D7) (u : D.what₂.Word)

open Classical

/- English proof (translation)
Rewrite using `[← (D.fm u).Fi_zero, ← ((D.fm u).emb_basis 0).2]`. Establish `hx` using `((D.fm u).lat 0).b.sum_repr x`. Rewrite using `[← hx, map_sum]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smulₛₗ]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`.
-/
theorem embedding_mem_forms_level_zero (x : ((D.fm u).lat 0).V) : (D.fm u).emb 0 x ∈ (D.mem u).A.Mu0 := by
  rw [← (D.fm u).Fi_zero, ← ((D.fm u).emb_basis 0).2]
  have hx := ((D.fm u).lat 0).b.sum_repr x
  rw [← hx, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/- English proof (translation)
Establish `key : ∀ v x, (D.fm u).emb 0 (t2sNm ((D.fm u).lat 0) ρ v x) = (D.mem u).A.Nm v ((D.fm u).emb 0 x)`. Introduce `v x`. Simplify using `only [t2sNm, ColumnsAtT.Nm, LinearMap.sum_apply, map_sum, hρ]`. Use extensionality with `x`. Simplify using `only [MemberForms.ramSub, Submodule.mem_comap, ColumnsAtT.Mram, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h⟩ v`. Apply `(D.fm u).emb_inj 0` to reduce the goal to its premises. Rewrite using `[key, h v, map_zero]`. Introduce `h`.

Conclude with `⟨embedding_mem_forms_level_zero D u x, fun v => by rw [← key, h v, map_zero]⟩`.
-/
theorem ramified_sub_eq_inf_norm_ker (ρ : (∀ v, t2sG D u v) →* Module.End D.what₂.LL ((D.fm u).lat 0).V)
    (hρ : ∀ v a x, (D.fm u).emb 0 (ρ (Pi.mulSingle v a) x) = (D.mem u).A.rhoT v a ((D.fm u).emb 0 x)) :
    (D.fm u).ramSub = ⨅ v, LinearMap.ker (t2sNm ((D.fm u).lat 0) ρ v) := by
  have key : ∀ v x, (D.fm u).emb 0 (t2sNm ((D.fm u).lat 0) ρ v x) = (D.mem u).A.Nm v ((D.fm u).emb 0 x) := by
    intro v x
    simp only [t2sNm, ColumnsAtT.Nm, LinearMap.sum_apply, map_sum, hρ]
  ext x
  simp only [MemberForms.ramSub, Submodule.mem_comap, ColumnsAtT.Mram, Submodule.mem_inf, Submodule.mem_iInf,
    LinearMap.mem_ker]
  constructor
  · rintro ⟨-, h⟩ v
    apply (D.fm u).emb_inj 0
    rw [key, h v, map_zero]
  · intro h
    exact ⟨embedding_mem_forms_level_zero D u x, fun v => by rw [← key, h v, map_zero]⟩

/- English proof (translation)
Take `⟨Wh, hW, hW0, Ψ, hΨ, hmaj, hL, hU⟩` from `induced_of_slice ((D.fm u).lat 0) ((D.fm u).lat_good 0) hL0 ρ W hbij horth hLc`. Conclude with `slope_formula_of_induced D u hS ⟨Wh, hW, hW0, Ψ, hΨ, hmaj, hL, (ramified_sub_eq_inf_norm_ker D u ρ hρ).trans hU⟩`.
-/
theorem slope_formula_of_slice (hS : Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u)
    (ρ : (∀ v, t2sG D u v) →* Module.End D.what₂.LL ((D.fm u).lat 0).V)
    (hρ : ∀ v a x, (D.fm u).emb 0 (ρ (Pi.mulSingle v a) x) = (D.mem u).A.rhoT v a ((D.fm u).emb 0 x))
    (W : Submodule D.what₂.LL ((D.fm u).lat 0).V)
    (hbij : Function.Bijective (t2sPsi ((D.fm u).lat 0) ρ W))
    (horth : ∀ v g h (x y : W), majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (ρ g (x : ((D.fm u).lat 0).V))
        (ρ h (y : ((D.fm u).lat 0).V)) =
      if g = h then majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (x : ((D.fm u).lat 0).V) (y : ((D.fm u).lat 0).V)
      else 0)
    (hLc : ∀ F : (∀ v, t2sG D u v) → W, t2sPsi ((D.fm u).lat 0) ρ W F ∈ ((D.fm u).lat 0).L ↔
      ∀ g, (F g : ((D.fm u).lat 0).V) ∈ ((D.fm u).lat 0).L)
    (hL0 : ((D.fm u).lat 0).L ≠ ⊥) : RamifiedSlopeFormula D u := by
  obtain ⟨Wh, hW, hW0, Ψ, hΨ, hmaj, hL, hU⟩ :=
    induced_of_slice ((D.fm u).lat 0) ((D.fm u).lat_good 0) hL0 ρ W hbij horth hLc
  exact slope_formula_of_induced D u hS ⟨Wh, hW, hW0, Ψ, hΨ, hmaj, hL, (ramified_sub_eq_inf_norm_ker D u ρ hρ).trans hU⟩

end AtDSlice

section Desc

variable {K V Y : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup Y] [Module ℂ Y] {σ : K →+* ℂ}

def t2sDesc (e : V →ₛₗ[σ] Y) (he : Function.Injective e) (R : Y →ₗ[ℂ] Y) (hR : ∀ x, ∃ y, e y = R (e x)) :
    V →ₗ[K] V where
  toFun x := (hR x).choose
  map_add' x x' := he (by
    rw [(hR (x + x')).choose_spec, map_add e (hR x).choose (hR x').choose, (hR x).choose_spec, (hR x').choose_spec,
      map_add, map_add])
  map_smul' c x := he (by
    rw [(hR (c • x)).choose_spec, RingHom.id_apply, map_smulₛₗ e c (hR x).choose, (hR x).choose_spec, map_smulₛₗ,
      map_smul])

/- English proof (translation)
The claim follows from `(hR x).choose_spec`.
-/
theorem t2sDesc_spec (e : V →ₛₗ[σ] Y) (he : Function.Injective e) (R : Y →ₗ[ℂ] Y) (hR : ∀ x, ∃ y, e y = R (e x))
    (x : V) : e (t2sDesc e he R hR x) = R (e x) := (hR x).choose_spec

end Desc

section Rho

variable {D : D7} {u : D.what₂.Word}

open Classical Formalism.L2.Forms

/- English proof (translation)
Establish `hx : x ∈ Submodule.span D.what₂.LL (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V)`. Rewrite using `[((D.fm u).lat_good 0).2.2]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨y, -, hy⟩` from `(D.fm u).rhoT_lat v a x hx`. Conclude with `⟨y, hy⟩`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x x' _ _ hx hx'`. Take `⟨y, hy⟩` from `hx`.

Take `⟨y', hy'⟩` from `hx'`. Conclude with `⟨y + y', by rw [map_add, hy, hy', map_add, map_add]⟩`. Consider the case `smul c x _ hx`. Take `⟨y, hy⟩` from `hx`. Conclude with `⟨c • y, by rw [map_smulₛₗ, hy, map_smulₛₗ, map_smul]⟩`.
-/
theorem rho_preserves_rational_forms (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (x : ((D.fm u).lat 0).V) :
    ∃ y, (D.fm u).emb 0 y = (D.mem u).A.rhoT v a ((D.fm u).emb 0 x) := by
  have hx : x ∈ Submodule.span D.what₂.LL (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V) := by
    rw [((D.fm u).lat_good 0).2.2]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, -, hy⟩ := (D.fm u).rhoT_lat v a x hx
    exact ⟨y, hy⟩
  | zero => exact ⟨0, by simp⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨y, hy⟩ := hx
    obtain ⟨y', hy'⟩ := hx'
    exact ⟨y + y', by rw [map_add, hy, hy', map_add, map_add]⟩
  | smul c x _ hx =>
    obtain ⟨y, hy⟩ := hx
    exact ⟨c • y, by rw [map_smulₛₗ, hy, map_smulₛₗ, map_smul]⟩

def t2sRv (v : (D.mem u).A.vT) : ((D.mem u).A.Fv v)ˣ →* Module.End D.what₂.LL ((D.fm u).lat 0).V where
  toFun a := t2sDesc ((D.fm u).emb 0) ((D.fm u).emb_inj 0) ((D.mem u).A.rhoT v a) (rho_preserves_rational_forms v a)
  map_one' := by
    apply LinearMap.ext; intro x
    apply (D.fm u).emb_inj 0
    rw [t2sDesc_spec, map_one]
    rfl
  map_mul' a b := by
    apply LinearMap.ext; intro x
    apply (D.fm u).emb_inj 0
    rw [t2sDesc_spec, map_mul, Module.End.mul_apply, Module.End.mul_apply, t2sDesc_spec, t2sDesc_spec]

/- English proof (translation)
The claim follows from `t2sDesc_spec _ ((D.fm u).emb_inj 0) _ _ x`.
-/
theorem t2sRv_spec (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (x : ((D.fm u).lat 0).V) :
    (D.fm u).emb 0 (t2sRv v a x) = (D.mem u).A.rhoT v a ((D.fm u).emb 0 x) :=
  t2sDesc_spec _ ((D.fm u).emb_inj 0) _ _ x

/- English proof (translation)
Rewrite using `[(D.fm u).Fi_zero]`. Conclude with `embedding_mem_forms_level_zero D u x`.
-/
theorem embedding_mem_forms (x : ((D.fm u).lat 0).V) : (D.fm u).emb 0 x ∈ (D.fm u).Fi 0 := by
  rw [(D.fm u).Fi_zero]; exact embedding_mem_forms_level_zero D u x

/- English proof (translation)
Introduce `v v' hvv a b`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Apply `(D.fm u).emb_inj 0` to reduce the goal to its premises. Use `show (D.fm u).emb 0 (t2sRv v a (t2sRv v' b x)) = (D.fm u).emb 0 (t2sRv v' b (t2sRv v a x))`.

Rewrite using `[t2sRv_spec, t2sRv_spec, t2sRv_spec, t2sRv_spec]`. Use `diamond_comm_distinct_places Tf hE 0 (Nat.zero_le _) v' v (Ne.symm hvv) a b ((D.fm u).emb 0 x) (embedding_mem_forms x)` as an intermediate fact. Rewrite `this` using `[diamond_eq_rho, diamond_eq_rho, diamond_eq_rho, diamond_eq_rho]`. Conclude with `this`.
-/
theorem t2sRv_comm (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) :
    Pairwise fun v v' => ∀ x y, Commute (t2sRv (D := D) (u := u) v x) (t2sRv v' y) := by
  intro v v' hvv a b
  apply LinearMap.ext; intro x
  apply (D.fm u).emb_inj 0
  show (D.fm u).emb 0 (t2sRv v a (t2sRv v' b x)) = (D.fm u).emb 0 (t2sRv v' b (t2sRv v a x))
  rw [t2sRv_spec, t2sRv_spec, t2sRv_spec, t2sRv_spec]
  have := diamond_comm_distinct_places Tf hE 0 (Nat.zero_le _) v' v (Ne.symm hvv) a b ((D.fm u).emb 0 x) (embedding_mem_forms x)
  rw [diamond_eq_rho, diamond_eq_rho, diamond_eq_rho, diamond_eq_rho] at this
  exact this

def t2sRho (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) :
    (∀ v, t2sG D u v) →* Module.End D.what₂.LL ((D.fm u).lat 0).V :=
  MonoidHom.noncommPiCoprod t2sRv (t2sRv_comm Tf hE)

/- English proof (translation)
Rewrite using `[t2sRho, MonoidHom.noncommPiCoprod_mulSingle, t2sRv_spec]`.
-/
theorem t2sRho_single (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ)
    (x : ((D.fm u).lat 0).V) :
    (D.fm u).emb 0 (t2sRho Tf hE (Pi.mulSingle v a) x) = (D.mem u).A.rhoT v a ((D.fm u).emb 0 x) := by
  rw [t2sRho, MonoidHom.noncommPiCoprod_mulSingle, t2sRv_spec]

end Rho

section Classes

variable {D : D7} {u : D.what₂.Word}

open Classical Formalism.L2.Forms

def t2sDv (v : (D.mem u).A.vT) : ((D.mem u).A.Fv v)ˣ →* Function.End ((D.mem u).C.cls 0) where
  toFun a := (D.fm u).dil 0 v a
  map_one' := by funext c; exact (D.fm u).dil_one 0 v c
  map_mul' a b := by funext c; exact (D.fm u).dil_mul 0 v a b c

/- English proof (translation)
Introduce `v v' hvv a b`. Use function extensionality and compare the values at `c`. Take `⟨ka, hka, δa, ha⟩` from `hE 0 (Nat.zero_le _) v a`. Take `⟨kb, hkb, δb, hb⟩` from `hE 0 (Nat.zero_le _) v' b`. Conclude with `dilation_commute_distinct Tf v v' hvv _ _ ka kb hka hkb δa δb ha hb c`.
-/
theorem t2sDv_comm (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) :
    Pairwise fun v v' => ∀ x y, Commute (t2sDv (D := D) (u := u) v x) (t2sDv v' y) := by
  intro v v' hvv a b
  funext c
  obtain ⟨ka, hka, δa, ha⟩ := hE 0 (Nat.zero_le _) v a
  obtain ⟨kb, hkb, δb, hb⟩ := hE 0 (Nat.zero_le _) v' b
  exact dilation_commute_distinct Tf v v' hvv _ _ ka kb hka hkb δa δb ha hb c

def t2sAc (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) : (∀ v, t2sG D u v) →* Function.End ((D.mem u).C.cls 0) :=
  MonoidHom.noncommPiCoprod t2sDv (t2sDv_comm Tf hE)

/- English proof (translation)
Rewrite using `[t2sAc, MonoidHom.noncommPiCoprod_mulSingle]`. Both sides reduce to the same expression.
-/
theorem t2sAc_single (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ)
    (c : (D.mem u).C.cls 0) : t2sAc Tf hE (Pi.mulSingle v a) c = (D.fm u).dil 0 v a c := by
  rw [t2sAc, MonoidHom.noncommPiCoprod_mulSingle]
  rfl

/- English proof (translation)
Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
theorem group_action_mul (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) (g h : ∀ v, t2sG D u v) (c : (D.mem u).C.cls 0) :
    t2sAc Tf hE (g * h) c = t2sAc Tf hE g (t2sAc Tf hE h c) := by
  rw [map_mul]; rfl

/- English proof (translation)
Rewrite using `[← Finset.univ_prod_mulSingle g]`. Use `Finset.prod_induction (fun i => Pi.mulSingle i (g i)) (fun g : ∀ v, t2sG D u v => ∀ c : (D.mem u).C.cls 0, ∃ e : ((D.mem u).C.Y 0 → ℂ) ≃ₗ[ℂ] ((D.mem u).C.Y 0 → ℂ), ∀ x, (D.fm u).emb 0 (t2sRho Tf hE g x) c = e ((D.fm u).emb 0 x (t2sAc Tf hE g c))) ?_ ?_ ?_` and prove the remaining obligations. Introduce `a b ha hb c`. Take `⟨ea, hea⟩` from `ha c`. Take `⟨eb, heb⟩` from `hb (t2sAc Tf hE a c)`.

Use `⟨eb.trans ea, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, Module.End.mul_apply, hea, heb, mul_comm a b, group_action_mul]`. Both sides reduce to the same expression. Introduce `c`. Use `⟨LinearEquiv.refl ℂ _, fun x => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_one, map_one]`. Both sides reduce to the same expression. Introduce `v _ c`. Use `⟨(D.fm u).dilT 0 v (g v) c, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[t2sRho_single, (D.fm u).rhoT_dil, t2sAc_single]`.
-/
theorem group_rep_transport_value (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) (g : ∀ v, t2sG D u v) :
    ∀ c : (D.mem u).C.cls 0, ∃ e : ((D.mem u).C.Y 0 → ℂ) ≃ₗ[ℂ] ((D.mem u).C.Y 0 → ℂ),
      ∀ x, (D.fm u).emb 0 (t2sRho Tf hE g x) c = e ((D.fm u).emb 0 x (t2sAc Tf hE g c)) := by
  rw [← Finset.univ_prod_mulSingle g]
  refine Finset.prod_induction (fun i => Pi.mulSingle i (g i))
    (fun g : ∀ v, t2sG D u v => ∀ c : (D.mem u).C.cls 0, ∃ e : ((D.mem u).C.Y 0 → ℂ) ≃ₗ[ℂ] ((D.mem u).C.Y 0 → ℂ),
      ∀ x, (D.fm u).emb 0 (t2sRho Tf hE g x) c = e ((D.fm u).emb 0 x (t2sAc Tf hE g c))) ?_ ?_ ?_
  · intro a b ha hb c
    obtain ⟨ea, hea⟩ := ha c
    obtain ⟨eb, heb⟩ := hb (t2sAc Tf hE a c)
    refine ⟨eb.trans ea, fun x => ?_⟩
    rw [map_mul, Module.End.mul_apply, hea, heb, mul_comm a b, group_action_mul]
    rfl
  · intro c
    refine ⟨LinearEquiv.refl ℂ _, fun x => ?_⟩
    rw [map_one, map_one]
    rfl
  · intro v _ c
    refine ⟨(D.fm u).dilT 0 v (g v) c, fun x => ?_⟩
    rw [t2sRho_single, (D.fm u).rhoT_dil, t2sAc_single]

def t2sPc [Fact (D.mem u).A.T.Prime] : (∀ v, t2sG D u v) ≃* ((D.mem u).A.vT → (ZMod (D.mem u).A.T)ˣ) :=
  MulEquiv.piCongrRight fun v => t2xU v

/- English proof (translation)
Use function extensionality and compare the values at `w`. Simplify using `only [t2sPc, MulEquiv.piCongrRight_apply]`. Break down `eq_or_ne w v with rfl | h` into its components or cases. Simplify using the standard rewrite rules. Simplify using `[Pi.mulSingle_eq_of_ne h]`.
-/
theorem t2sPc_single [Fact (D.mem u).A.T.Prime] (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) :
    t2sPc (D := D) (u := u) (Pi.mulSingle v a) = Pi.mulSingle v (t2xU v a) := by
  funext w
  simp only [t2sPc, MulEquiv.piCongrRight_apply]
  rcases eq_or_ne w v with rfl | h
  · simp
  · simp [Pi.mulSingle_eq_of_ne h]

/- English proof (translation)
Rewrite using `[← Finset.univ_prod_mulSingle g]`. Use `Finset.prod_induction (fun i => Pi.mulSingle i (g i)) (fun g : ∀ v, t2sG D u v => ∀ c, t2sAc Tf hE g c = t2xAc Tf hE (t2sPc g) c) ?_ ?_ ?_` and prove the remaining obligations. Introduce `a b ha hb c`. Rewrite using `[group_action_mul, hb, ha, map_mul, map_mul]`. Both sides reduce to the same expression.

Introduce `c`. Rewrite using `[map_one, map_one, map_one]`. Introduce `v _ c`. Rewrite using `[t2sAc_single, t2sPc_single, group_action_mulSingle_eq_dilation, MulEquiv.symm_apply_apply]`.
-/
theorem group_action_eq_unit_action [Fact (D.mem u).A.T.Prime] (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) (g : ∀ v, t2sG D u v) :
    ∀ c, t2sAc Tf hE g c = t2xAc Tf hE (t2sPc g) c := by
  rw [← Finset.univ_prod_mulSingle g]
  refine Finset.prod_induction (fun i => Pi.mulSingle i (g i))
    (fun g : ∀ v, t2sG D u v => ∀ c, t2sAc Tf hE g c = t2xAc Tf hE (t2sPc g) c) ?_ ?_ ?_
  · intro a b ha hb c
    rw [group_action_mul, hb, ha, map_mul, map_mul]
    rfl
  · intro c
    rw [map_one, map_one, map_one]
  · intro v _ c
    rw [t2sAc_single, t2sPc_single, group_action_mulSingle_eq_dilation, MulEquiv.symm_apply_apply]

/- English proof (translation)
Use `haveI : Fact (D.mem u).A.T.Prime := ⟨(D.mem u).A.T_prime⟩`. Establish `h1` using `group_acts_freely_classes Tf hS hE (t2sPc g) c (by rw [← group_action_eq_unit_action]; exact h)`. Conclude with `t2sPc.injective (h1.trans (map_one _).symm)`.
-/
theorem group_acts_freely_classes' (Tf : FormsTied D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (hE : DiamondElementsExist Tf) (g : ∀ v, t2sG D u v)
    (c : (D.mem u).C.cls 0) (h : t2sAc Tf hE g c = c) : g = 1 := by
  haveI : Fact (D.mem u).A.T.Prime := ⟨(D.mem u).A.T_prime⟩
  have h1 := group_acts_freely_classes Tf hS hE (t2sPc g) c (by rw [← group_action_eq_unit_action]; exact h)
  exact t2sPc.injective (h1.trans (map_one _).symm)

end Classes

section SliceTied

variable {D : D7} {u : D.what₂.Word}

open Classical Formalism.L2.Forms

/- English proof (translation)
Establish `hr` using `((Tf.val 0 (Nat.zero_le _)).rat ((D.fm u).emb 0 x)).1 ⟨x, rfl⟩`. Establish `h0 : (D.fm u).emb 0 x ∈ (D.mem u).A.Mu0` using `by rw [← (D.fm u).Fi_zero]; exact hr.1`. Rewrite `h0` using `[mem_forms_level_zero_iff Tf hS]`. Use `((Tf.val 0 (Nat.zero_le _)).rat _).2 ⟨?_, fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[(D.fm u).Fi_zero, mem_forms_level_zero_iff Tf hS]`.

Introduce `c`. Distinguish the cases in `hc : S c`. Simplify using `only [hc, if_true]`. Conclude with `h0 c`. Simplify using `only [hc, if_false]`.

Conclude with `(levelZeroValues Tf).zero_mem`. Distinguish the cases in `hc : S c`. Simplify using `only [hc, if_true]`. Conclude with `hr.2 c`. Use `⟨0, zero_mem _, fun z => ?_⟩` and prove the remaining obligations.

Simplify using `only [hc, if_false, map_zero, Pi.zero_apply]`.
-/
theorem restriction_rational_form (Tf : FormsTied D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (x : ((D.fm u).lat 0).V)
    (S : (D.mem u).C.cls 0 → Prop) :
    ∃ y, (D.fm u).emb 0 y = fun c => if S c then (D.fm u).emb 0 x c else 0 := by
  have hr := ((Tf.val 0 (Nat.zero_le _)).rat ((D.fm u).emb 0 x)).1 ⟨x, rfl⟩
  have h0 : (D.fm u).emb 0 x ∈ (D.mem u).A.Mu0 := by rw [← (D.fm u).Fi_zero]; exact hr.1
  rw [mem_forms_level_zero_iff Tf hS] at h0
  refine ((Tf.val 0 (Nat.zero_le _)).rat _).2 ⟨?_, fun c => ?_⟩
  · rw [(D.fm u).Fi_zero, mem_forms_level_zero_iff Tf hS]
    intro c
    by_cases hc : S c
    · simp only [hc, if_true]; exact h0 c
    · simp only [hc, if_false]; exact (levelZeroValues Tf).zero_mem
  · by_cases hc : S c
    · simp only [hc, if_true]; exact hr.2 c
    · refine ⟨0, zero_mem _, fun z => ?_⟩
      simp only [hc, if_false, map_zero, Pi.zero_apply]

/- English proof (translation)
Introduce `h0`. Establish `hV : ∀ x : ((D.fm u).lat 0).V, x = 0`. Introduce `x`. Establish `hx : x ∈ Submodule.span D.what₂.LL (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V)`. Rewrite using `[((D.fm u).lat_good 0).2.2]`.

Discharge the goal by the elementary cases of `trivial`. Rewrite `hx` using `[h0, Submodule.bot_coe, Submodule.span_zero_singleton]`. Conclude with `(Submodule.mem_bot _).1 hx`. Take `⟨c0, -⟩` from `(Tf.cls 0 (Nat.zero_le _)).y_bij.2 (Quotient.mk'' 1)`. Take `⟨w, hw, hw0⟩` from `level_zero_values_ne_bot Tf`.

Establish `hmem : (Pi.single c0 w : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) ∈ (D.mem u).A.Mu0`. Rewrite using `[mem_forms_level_zero_iff Tf hS]`. Introduce `c`. Distinguish the cases in `hc : c = c0`. Substitute `hc` using the available equality.

Rewrite using `[Pi.single_eq_same]`. Conclude with `hw`. Rewrite using `[Pi.single_eq_of_ne hc]`. Conclude with `(levelZeroValues Tf).zero_mem`. Rewrite `hmem` using `[← (D.fm u).Fi_zero, ← ((D.fm u).emb_basis 0).2]`.

Establish `hsp : Submodule.span ℂ (Set.range fun a => (D.fm u).emb 0 (((D.fm u).lat 0).b a)) = ⊥`. Rewrite using `[Submodule.span_eq_bot]`. Introduce and unpack `_ ⟨a, rfl⟩`. Use `show (D.fm u).emb 0 (((D.fm u).lat 0).b a) = 0`. Rewrite using `[hV (((D.fm u).lat 0).b a), map_zero]`.

Rewrite `hmem` using `[hsp, Submodule.mem_bot]`. Apply `hw0` to reduce the goal to its premises. Use `congrFun hmem c0` as an intermediate fact. Simplify using `using this`.
-/
theorem lattice_level_zero_ne_bot (Tf : FormsTied D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) : ((D.fm u).lat 0).L ≠ ⊥ := by
  intro h0
  have hV : ∀ x : ((D.fm u).lat 0).V, x = 0 := by
    intro x
    have hx : x ∈ Submodule.span D.what₂.LL (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V) := by
      rw [((D.fm u).lat_good 0).2.2]; trivial
    rw [h0, Submodule.bot_coe, Submodule.span_zero_singleton] at hx
    exact (Submodule.mem_bot _).1 hx
  obtain ⟨c0, -⟩ := (Tf.cls 0 (Nat.zero_le _)).y_bij.2 (Quotient.mk'' 1)
  obtain ⟨w, hw, hw0⟩ := level_zero_values_ne_bot Tf
  have hmem : (Pi.single c0 w : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) ∈ (D.mem u).A.Mu0 := by
    rw [mem_forms_level_zero_iff Tf hS]
    intro c
    by_cases hc : c = c0
    · subst hc; rw [Pi.single_eq_same]; exact hw
    · rw [Pi.single_eq_of_ne hc]; exact (levelZeroValues Tf).zero_mem
  rw [← (D.fm u).Fi_zero, ← ((D.fm u).emb_basis 0).2] at hmem
  have hsp : Submodule.span ℂ (Set.range fun a => (D.fm u).emb 0 (((D.fm u).lat 0).b a)) = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro _ ⟨a, rfl⟩
    show (D.fm u).emb 0 (((D.fm u).lat 0).b a) = 0
    rw [hV (((D.fm u).lat 0).b a), map_zero]
  rw [hsp, Submodule.mem_bot] at hmem
  apply hw0
  have := congrFun hmem c0
  simpa using this

variable (Tf : FormsTied D u) (hE : DiamondElementsExist Tf)

def t2sSetoid : Setoid ((D.mem u).C.cls 0) where
  r a b := ∃ g, t2sAc Tf hE g b = a
  iseqv := by
    refine ⟨fun a => ⟨1, by rw [map_one]; rfl⟩, fun {a b} ⟨g, hg⟩ => ⟨g⁻¹, ?_⟩, fun {a b c} ⟨g, hg⟩ ⟨h, hh⟩ => ⟨g * h, ?_⟩⟩
    · rw [← hg, ← group_action_mul, inv_mul_cancel, map_one]; rfl
    · rw [group_action_mul, hh, hg]

def t2sRep (c : (D.mem u).C.cls 0) : (D.mem u).C.cls 0 :=
  (Quotient.mk (t2sSetoid Tf hE) c).out

/- English proof (translation)
The claim follows from `Quotient.mk_out (s := t2sSetoid Tf hE) c`.
-/
theorem t2sRep_spec (c : (D.mem u).C.cls 0) : ∃ g, t2sAc Tf hE g c = t2sRep Tf hE c :=
  Quotient.mk_out (s := t2sSetoid Tf hE) c

/- English proof (translation)
Unfold `t2sRep`. Rewrite using `[Quotient.sound (s := t2sSetoid Tf hE) h]`.
-/
theorem t2sRep_eq {a b : (D.mem u).C.cls 0} (h : ∃ g, t2sAc Tf hE g b = a) : t2sRep Tf hE a = t2sRep Tf hE b := by
  unfold t2sRep
  rw [Quotient.sound (s := t2sSetoid Tf hE) h]

/- English proof (translation)
The claim follows from `t2sRep_eq Tf hE ⟨g, rfl⟩`.
-/
theorem t2sRep_ac (g) (c : (D.mem u).C.cls 0) : t2sRep Tf hE (t2sAc Tf hE g c) = t2sRep Tf hE c :=
  t2sRep_eq Tf hE ⟨g, rfl⟩

def t2sH (c : (D.mem u).C.cls 0) : ∀ v, t2sG D u v := (t2sRep_spec Tf hE c).choose

/- English proof (translation)
The claim follows from `(t2sRep_spec Tf hE c).choose_spec`.
-/
theorem class_rep_group_elem_spec (c : (D.mem u).C.cls 0) : t2sAc Tf hE (t2sH Tf hE c) c = t2sRep Tf hE c :=
  (t2sRep_spec Tf hE c).choose_spec

/- English proof (translation)
Establish `h1 : t2sAc Tf hE (g⁻¹ * g') c = c`. Rewrite using `[group_action_mul, ← h, ← group_action_mul, inv_mul_cancel, map_one]`. Both sides reduce to the same expression. Establish `h2` using `group_acts_freely_classes' Tf hS hE _ c h1`. Rewrite `h2` using `[inv_mul_eq_one]`.

Conclude with `h2`.
-/
theorem group_action_injective (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) {g g' : ∀ v, t2sG D u v} {c : (D.mem u).C.cls 0}
    (h : t2sAc Tf hE g c = t2sAc Tf hE g' c) : g = g' := by
  have h1 : t2sAc Tf hE (g⁻¹ * g') c = c := by
    rw [group_action_mul, ← h, ← group_action_mul, inv_mul_cancel, map_one]; rfl
  have h2 := group_acts_freely_classes' Tf hS hE _ c h1
  rw [inv_mul_eq_one] at h2
  exact h2

/- English proof (translation)
The claim follows from `group_action_injective Tf hE hS (h.trans (class_rep_group_elem_spec Tf hE c).symm)`.
-/
theorem class_rep_group_elem_unique (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) {g : ∀ v, t2sG D u v} {c : (D.mem u).C.cls 0}
    (h : t2sAc Tf hE g c = t2sRep Tf hE c) : g = t2sH Tf hE c :=
  group_action_injective Tf hE hS (h.trans (class_rep_group_elem_spec Tf hE c).symm)

def t2sW : Submodule D.what₂.LL ((D.fm u).lat 0).V where
  carrier := {x | ∀ c, t2sRep Tf hE c ≠ c → (D.fm u).emb 0 x c = 0}
  add_mem' {x y} hx hy c hc := by rw [map_add, Pi.add_apply, hx c hc, hy c hc, add_zero]
  zero_mem' c _ := by rw [map_zero]; rfl
  smul_mem' r x hx c hc := by rw [map_smulₛₗ, Pi.smul_apply, hx c hc, smul_zero]

/- English proof (translation)
Take `⟨e, he⟩` from `group_rep_transport_value Tf hE g c`. Rewrite using `[he]`. Establish `hn : t2sRep Tf hE (t2sAc Tf hE g c) ≠ t2sAc Tf hE g c`. Introduce `h`. Rewrite `h` using `[t2sRep_ac]`.

Conclude with `hg (class_rep_group_elem_unique Tf hE hS h.symm)`. Rewrite using `[(F g).2 _ hn, map_zero]`.
-/
theorem slice_value_off_summand (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (F : (∀ v, t2sG D u v) → t2sW Tf hE) (g : ∀ v, t2sG D u v)
    (c : (D.mem u).C.cls 0) (hg : g ≠ t2sH Tf hE c) :
    (D.fm u).emb 0 (t2sRho Tf hE g (F g : ((D.fm u).lat 0).V)) c = 0 := by
  obtain ⟨e, he⟩ := group_rep_transport_value Tf hE g c
  rw [he]
  have hn : t2sRep Tf hE (t2sAc Tf hE g c) ≠ t2sAc Tf hE g c := by
    intro h
    rw [t2sRep_ac] at h
    exact hg (class_rep_group_elem_unique Tf hE hS h.symm)
  rw [(F g).2 _ hn, map_zero]

/- English proof (translation)
Rewrite using `[t2sPsi_apply, map_sum, Finset.sum_apply, Finset.sum_eq_single (t2sH Tf hE c)]`. Introduce `g _ hg`. Conclude with `slice_value_off_summand Tf hE hS F g c hg`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem slice_map_value_at_class (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (F : (∀ v, t2sG D u v) → t2sW Tf hE) (c : (D.mem u).C.cls 0) :
    (D.fm u).emb 0 (t2sPsi ((D.fm u).lat 0) (t2sRho Tf hE) (t2sW Tf hE) F) c =
      (D.fm u).emb 0 (t2sRho Tf hE (t2sH Tf hE c) (F (t2sH Tf hE c) : ((D.fm u).lat 0).V)) c := by
  rw [t2sPsi_apply, map_sum, Finset.sum_apply, Finset.sum_eq_single (t2sH Tf hE c)]
  · intro g _ hg
    exact slice_value_off_summand Tf hE hS F g c hg
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `F F' hFF`. Establish `hz : ∀ F0 : (∀ v, t2sG D u v) → t2sW Tf hE, t2sPsi ((D.fm u).lat 0) (t2sRho Tf hE) (t2sW Tf hE) F0 = 0 → F0 = 0`. Introduce `F0 h0`. Use function extensionality and compare the values at `g`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `(D.fm u).emb_inj 0` to reduce the goal to its premises. Use function extensionality and compare the values at `r`. Use `show (D.fm u).emb 0 (F0 g : ((D.fm u).lat 0).V) r = (D.fm u).emb 0 0 r`. Rewrite using `[map_zero]`.

Distinguish the cases in `hr : t2sRep Tf hE r = r`. Use `set c := t2sAc Tf hE g⁻¹ r with hc`. Establish `hgc : t2sAc Tf hE g c = r`. Rewrite using `[hc, ← group_action_mul, mul_inv_cancel, map_one]`. Both sides reduce to the same expression.

Establish `hrep : t2sAc Tf hE g c = t2sRep Tf hE c`. Rewrite using `[hgc, hc, t2sRep_ac, hr]`. Establish `hH` using `class_rep_group_elem_unique Tf hE hS hrep`. Establish `h1` using `slice_map_value_at_class Tf hE hS F0 c`. Rewrite `h1` using `[h0, map_zero, ← hH]`.

Take `⟨e, he⟩` from `group_rep_transport_value Tf hE g c`. Rewrite `h1` using `[he, hgc]`. Establish `h2` using `congrFun h1.symm`. Conclude with `(e.map_eq_zero_iff).1 (funext fun z => by simpa using congrFun h1.symm z)`. Conclude with `(F0 g).2 r hr`.

Use `hz (F - F') (by rw [map_sub, hFF, sub_self])` as an intermediate fact. Conclude with `sub_eq_zero.1 this`. Introduce `x`. Establish `hy` using `fun g : ∀ v, t2sG D u v => restriction_rational_form Tf hS x (fun c => t2sH Tf hE c = g)`. Use `choose y hy using hy`.

Establish `hmem : ∀ g, t2sRho Tf hE g⁻¹ (y g) ∈ t2sW Tf hE`. Introduce `g c hc`. Take `⟨e, he⟩` from `group_rep_transport_value Tf hE g⁻¹ c`. Rewrite using `[he, hy g]`. Establish `hne : t2sH Tf hE (t2sAc Tf hE g⁻¹ c) ≠ g`.

Introduce `h`. Establish `h1` using `class_rep_group_elem_spec Tf hE (t2sAc Tf hE g⁻¹ c)`. Rewrite `h1` using `[h, ← group_action_mul, mul_inv_cancel, map_one, t2sRep_ac]`. Conclude with `hc h1.symm`. Simplify using `only [hne, if_false, map_zero]`.

Use `⟨fun g => ⟨_, hmem g⟩, ?_⟩` and prove the remaining obligations. Apply `(D.fm u).emb_inj 0` to reduce the goal to its premises. Use function extensionality and compare the values at `c`. Rewrite using `[slice_map_value_at_class Tf hE hS]`. Use `show (D.fm u).emb 0 (t2sRho Tf hE (t2sH Tf hE c) (t2sRho Tf hE (t2sH Tf hE c)⁻¹ (y (t2sH Tf hE c)))) c = _`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, hy]`. Simplify using the standard rewrite rules.
-/
theorem slice_map_bijective (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) :
    Function.Bijective (t2sPsi ((D.fm u).lat 0) (t2sRho Tf hE) (t2sW Tf hE)) := by
  constructor
  · intro F F' hFF
    have hz : ∀ F0 : (∀ v, t2sG D u v) → t2sW Tf hE,
        t2sPsi ((D.fm u).lat 0) (t2sRho Tf hE) (t2sW Tf hE) F0 = 0 → F0 = 0 := by
      intro F0 h0
      funext g
      apply Subtype.ext
      apply (D.fm u).emb_inj 0
      funext r
      show (D.fm u).emb 0 (F0 g : ((D.fm u).lat 0).V) r = (D.fm u).emb 0 0 r
      rw [map_zero]
      by_cases hr : t2sRep Tf hE r = r
      · set c := t2sAc Tf hE g⁻¹ r with hc
        have hgc : t2sAc Tf hE g c = r := by
          rw [hc, ← group_action_mul, mul_inv_cancel, map_one]; rfl
        have hrep : t2sAc Tf hE g c = t2sRep Tf hE c := by
          rw [hgc, hc, t2sRep_ac, hr]
        have hH := class_rep_group_elem_unique Tf hE hS hrep
        have h1 := slice_map_value_at_class Tf hE hS F0 c
        rw [h0, map_zero, ← hH] at h1
        obtain ⟨e, he⟩ := group_rep_transport_value Tf hE g c
        rw [he, hgc] at h1
        have h2 := congrFun h1.symm
        exact (e.map_eq_zero_iff).1 (funext fun z => by simpa using congrFun h1.symm z)
      · exact (F0 g).2 r hr
    have := hz (F - F') (by rw [map_sub, hFF, sub_self])
    exact sub_eq_zero.1 this
  · intro x
    have hy := fun g : ∀ v, t2sG D u v => restriction_rational_form Tf hS x (fun c => t2sH Tf hE c = g)
    choose y hy using hy
    have hmem : ∀ g, t2sRho Tf hE g⁻¹ (y g) ∈ t2sW Tf hE := by
      intro g c hc
      obtain ⟨e, he⟩ := group_rep_transport_value Tf hE g⁻¹ c
      rw [he, hy g]
      have hne : t2sH Tf hE (t2sAc Tf hE g⁻¹ c) ≠ g := by
        intro h
        have h1 := class_rep_group_elem_spec Tf hE (t2sAc Tf hE g⁻¹ c)
        rw [h, ← group_action_mul, mul_inv_cancel, map_one, t2sRep_ac] at h1
        exact hc h1.symm
      simp only [hne, if_false, map_zero]
    refine ⟨fun g => ⟨_, hmem g⟩, ?_⟩
    apply (D.fm u).emb_inj 0
    funext c
    rw [slice_map_value_at_class Tf hE hS]
    show (D.fm u).emb 0 (t2sRho Tf hE (t2sH Tf hE c) (t2sRho Tf hE (t2sH Tf hE c)⁻¹ (y (t2sH Tf hE c)))) c = _
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, hy]
    simp

/- English proof (translation)
Rewrite using `[← Finset.univ_prod_mulSingle g]`. Use `Finset.prod_induction (fun i => Pi.mulSingle i (g i)) (fun g : ∀ v, t2sG D u v => ∀ x ∈ ((D.fm u).lat 0).L, t2sRho Tf hE g x ∈ ((D.fm u).lat 0).L) ?_ ?_ ?_` and prove the remaining obligations. Introduce `a b ha hb x hx`. Rewrite using `[map_mul, Module.End.mul_apply]`. Conclude with `ha _ (hb x hx)`.

Introduce `x hx`. Rewrite using `[map_one]`. Conclude with `hx`. Introduce `v _ x hx`. Take `⟨y, hyL, hy⟩` from `(D.fm u).rhoT_lat v (g v) x hx`.

Establish `: y = t2sRho Tf hE (Pi.mulSingle v (g v)) x` using `(D.fm u).emb_inj 0 (by rw [hy, t2sRho_single])`. Rewrite using `[← this]`. Conclude with `hyL`.
-/
theorem group_rep_preserves_lattice (g : ∀ v, t2sG D u v) : ∀ x ∈ ((D.fm u).lat 0).L, t2sRho Tf hE g x ∈ ((D.fm u).lat 0).L := by
  rw [← Finset.univ_prod_mulSingle g]
  refine Finset.prod_induction (fun i => Pi.mulSingle i (g i))
    (fun g : ∀ v, t2sG D u v => ∀ x ∈ ((D.fm u).lat 0).L, t2sRho Tf hE g x ∈ ((D.fm u).lat 0).L) ?_ ?_ ?_
  · intro a b ha hb x hx
    rw [map_mul, Module.End.mul_apply]
    exact ha _ (hb x hx)
  · intro x hx
    rw [map_one]; exact hx
  · intro v _ x hx
    obtain ⟨y, hyL, hy⟩ := (D.fm u).rhoT_lat v (g v) x hx
    have : y = t2sRho Tf hE (Pi.mulSingle v (g v)) x := (D.fm u).emb_inj 0 (by rw [hy, t2sRho_single])
    rw [← this]; exact hyL

def t2sQ (c : (D.mem u).C.cls 0) (f : (D.mem u).C.Y 0 → ℂ) : Prop :=
  ∀ (w : D.what₂.places.Pl) (B : GL (Fin (D.R.N 0)) D.host.E),
    IsLocBasis (D.what₂.places.resChar w)
      (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) (clsCrd D u 0 (Nat.zero_le _) c)) B →
    ∃ P ∈ IntSpan D w ((D.fm u).lam 0),
      ∀ z, f z = fnOf _ (shiftOf (lamT u 0)) (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1) P
        ((Tf.val 0 (Nat.zero_le _)).eY z)

/- English proof (translation)
Introduce `w B _` and use `⟨0, zero_mem _, fun z => by simp⟩`.
-/
theorem local_integral_zero (c : (D.mem u).C.cls 0) : t2sQ Tf c 0 := fun w B _ => ⟨0, zero_mem _, fun z => by simp⟩

/- English proof (translation)
Rewrite using `[(Tf.val 0 (Nat.zero_le _)).lat x]`. Conclude with `⟨fun h c w B hB => h w c B hB, fun h w c B hB => h c w B hB⟩`.
-/
theorem mem_lattice_iff_local (x : ((D.fm u).lat 0).V) : x ∈ ((D.fm u).lat 0).L ↔ ∀ c, t2sQ Tf c ((D.fm u).emb 0 x c) := by
  rw [(Tf.val 0 (Nat.zero_le _)).lat x]
  exact ⟨fun h c w B hB => h w c B hB, fun h w c B hB => h c w B hB⟩

/- English proof (translation)
Establish `hρ : ∀ g, (F g : ((D.fm u).lat 0).V) ∈ ((D.fm u).lat 0).L ↔ t2sRho Tf hE g (F g : ((D.fm u).lat 0).V) ∈ ((D.fm u).lat 0).L`. Introduce `g`. Use `⟨group_rep_preserves_lattice Tf hE g _, fun h => ?_⟩` and prove the remaining obligations. Use `group_rep_preserves_lattice Tf hE g⁻¹ _ h` as an intermediate fact. Rewrite `this` using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Then use the resulting hypothesis.

Simplify using `only [hρ, mem_lattice_iff_local Tf, slice_map_value_at_class Tf hE hS]`. Prove the components needed by the constructor for the conclusion. Introduce `h g c`. Distinguish the cases in `hg : g = t2sH Tf hE c`. Substitute `hg` using the available equality.

Conclude with `h c`. Rewrite using `[slice_value_off_summand Tf hE hS F g c hg]`. Conclude with `local_integral_zero Tf c`. Introduce `h c`. Conclude with `h _ c`.
-/
theorem slice_mem_lattice_iff (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (F : (∀ v, t2sG D u v) → t2sW Tf hE) :
    t2sPsi ((D.fm u).lat 0) (t2sRho Tf hE) (t2sW Tf hE) F ∈ ((D.fm u).lat 0).L ↔
      ∀ g, (F g : ((D.fm u).lat 0).V) ∈ ((D.fm u).lat 0).L := by
  have hρ : ∀ g, (F g : ((D.fm u).lat 0).V) ∈ ((D.fm u).lat 0).L ↔
      t2sRho Tf hE g (F g : ((D.fm u).lat 0).V) ∈ ((D.fm u).lat 0).L := by
    intro g
    refine ⟨group_rep_preserves_lattice Tf hE g _, fun h => ?_⟩
    have := group_rep_preserves_lattice Tf hE g⁻¹ _ h
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this
  simp only [hρ, mem_lattice_iff_local Tf, slice_map_value_at_class Tf hE hS]
  constructor
  · intro h g c
    by_cases hg : g = t2sH Tf hE c
    · subst hg; exact h c
    · rw [slice_value_off_summand Tf hE hS F g c hg]; exact local_integral_zero Tf c
  · intro h c
    exact h _ c

end SliceTied

section AtDTied

variable (D : D7) (u : D.what₂.Word)

open Classical Formalism.L2.Forms

/- English proof (translation)
The claim follows from `slope_formula_of_slice D u hS (t2sRho Tf hE) (fun v a x => t2sRho_single Tf hE v a x) W hbij horth hLc hL0`.
-/
theorem slope_formula_of_compatible_slice (hS : Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u) (Tf : FormsTied D u) (hE : DiamondElementsExist Tf)
    (W : Submodule D.what₂.LL ((D.fm u).lat 0).V)
    (hbij : Function.Bijective (t2sPsi ((D.fm u).lat 0) (t2sRho Tf hE) W))
    (horth : ∀ v g h (x y : W), majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v
        (t2sRho Tf hE g (x : ((D.fm u).lat 0).V)) (t2sRho Tf hE h (y : ((D.fm u).lat 0).V)) =
      if g = h then majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (x : ((D.fm u).lat 0).V) (y : ((D.fm u).lat 0).V)
      else 0)
    (hLc : ∀ F : (∀ v, t2sG D u v) → W, t2sPsi ((D.fm u).lat 0) (t2sRho Tf hE) W F ∈ ((D.fm u).lat 0).L ↔
      ∀ g, (F g : ((D.fm u).lat 0).V) ∈ ((D.fm u).lat 0).L)
    (hL0 : ((D.fm u).lat 0).L ≠ ⊥) : RamifiedSlopeFormula D u :=
  slope_formula_of_slice D u hS (t2sRho Tf hE) (fun v a x => t2sRho_single Tf hE v a x) W hbij horth hLc hL0

end AtDTied

section Final

variable (D : D7) (u : D.what₂.Word)

open Classical Formalism.L2.Forms

def MetricOrthogonalClasses : Prop :=
  ∀ (v : InfinitePlace D.what₂.LL) (x y : ((D.fm u).lat 0).V),
    (∀ c, (D.fm u).emb 0 x c = 0 ∨ (D.fm u).emb 0 y c = 0) →
      majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y = 0

def DiamondIsometry : Prop :=
  ∀ (v : InfinitePlace D.what₂.LL) (w : (D.mem u).A.vT) (a : ((D.mem u).A.Fv w)ˣ) (x y : ((D.fm u).lat 0).V),
    majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (t2sRv w a x) (t2sRv w a y) =
      majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y

variable {D u}

/- English proof (translation)
Rewrite using `[← Finset.univ_prod_mulSingle g]`. Use `Finset.prod_induction (fun i => Pi.mulSingle i (g i)) (fun g : ∀ v, t2sG D u v => ∀ (v : InfinitePlace D.what₂.LL) (x y : ((D.fm u).lat 0).V), majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (t2sRho Tf hE g x) (t2sRho Tf hE g y) = majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y) …` and prove the remaining obligations. Introduce `a b ha hb v x y`. Rewrite using `[map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, hb]`. Introduce `v x y`.

Rewrite using `[map_one]`. Both sides reduce to the same expression. Introduce `w _ v x y`. Rewrite using `[t2sRho, MonoidHom.noncommPiCoprod_mulSingle]`. Conclude with `hI v w (g w) x y`.
-/
theorem group_rep_majorant_isometry (hI : DiamondIsometry D u) (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) (g : ∀ v, t2sG D u v) :
    ∀ (v : InfinitePlace D.what₂.LL) (x y : ((D.fm u).lat 0).V),
      majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (t2sRho Tf hE g x) (t2sRho Tf hE g y) =
        majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y := by
  rw [← Finset.univ_prod_mulSingle g]
  refine Finset.prod_induction (fun i => Pi.mulSingle i (g i))
    (fun g : ∀ v, t2sG D u v => ∀ (v : InfinitePlace D.what₂.LL) (x y : ((D.fm u).lat 0).V),
      majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (t2sRho Tf hE g x) (t2sRho Tf hE g y) =
        majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y) ?_ ?_ ?_
  · intro a b ha hb v x y
    rw [map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, hb]
  · intro v x y
    rw [map_one]; rfl
  · intro w _ v x y
    rw [t2sRho, MonoidHom.noncommPiCoprod_mulSingle]
    exact hI v w (g w) x y

/- English proof (translation)
Introduce `v g h x y`. Distinguish the cases in `hgh : g = h`. Substitute `hgh` using the available equality. Apply the tactic sequence `rw [if_pos rfl, group_rep_majorant_isometry hI Tf hE]`. Rewrite using `[if_neg hgh]`.

Apply `hO` to reduce the goal to its premises. Introduce `c`. Distinguish the cases in `hc : g = t2sH Tf hE c`. Use `right`. Conclude with `slice_value_off_summand Tf hE hS (fun _ => y) h c (fun e => hgh (hc.trans e.symm))`.

Use `left`. Conclude with `slice_value_off_summand Tf hE hS (fun _ => x) g c hc`.
-/
theorem slice_summands_orthogonal (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (hO : MetricOrthogonalClasses D u) (hI : DiamondIsometry D u) (Tf : FormsTied D u)
    (hE : DiamondElementsExist Tf) :
    ∀ v g h (x y : t2sW Tf hE), majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v
        (t2sRho Tf hE g (x : ((D.fm u).lat 0).V)) (t2sRho Tf hE h (y : ((D.fm u).lat 0).V)) =
      if g = h then majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (x : ((D.fm u).lat 0).V) (y : ((D.fm u).lat 0).V)
      else 0 := by
  intro v g h x y
  by_cases hgh : g = h
  · subst hgh
    rw [if_pos rfl, group_rep_majorant_isometry hI Tf hE]
  · rw [if_neg hgh]
    apply hO
    intro c
    by_cases hc : g = t2sH Tf hE c
    · right
      exact slice_value_off_summand Tf hE hS (fun _ => y) h c (fun e => hgh (hc.trans e.symm))
    · left
      exact slice_value_off_summand Tf hE hS (fun _ => x) g c hc

/- English proof (translation)
The claim follows from `slope_formula_of_compatible_slice D u hS Tf hE (t2sW Tf hE) (slice_map_bijective Tf hE hA) (slice_summands_orthogonal hA hO hI Tf hE) (slice_mem_lattice_iff Tf hE hA) (lattice_level_zero_ne_bot Tf hA)`.
-/
theorem slope_formula_of_diamonds (hS : Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u) (Tf : FormsTied D u) (hA : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (hE : DiamondElementsExist Tf)
    (hO : MetricOrthogonalClasses D u) (hI : DiamondIsometry D u) : RamifiedSlopeFormula D u :=
  slope_formula_of_compatible_slice D u hS Tf hE (t2sW Tf hE) (slice_map_bijective Tf hE hA) (slice_summands_orthogonal hA hO hI Tf hE) (slice_mem_lattice_iff Tf hE hA)
    (lattice_level_zero_ne_bot Tf hA)

end Final

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
