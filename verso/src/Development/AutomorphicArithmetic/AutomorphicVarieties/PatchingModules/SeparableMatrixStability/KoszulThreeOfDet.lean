import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.OdComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.CocKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.KerOo

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

/- English proof (translation)
Introduce `l _ L G0 T Λ n x k al hP hE`. Introduce `z hz`. Establish `hρ : ∀ g, x.ρX x.A g = mat x.ρ g`. Introduce `g`. Use extensionality with `i j`.

Simplify using `[NP.ρX]`. Establish `hzero : ∀ j, z (Λ.ta j) = 0`. Introduce `j`. Establish `hc` using `Λ.comm j`. Establish `h1` using `hz.2.2.1 (Λ.ph j) (Λ.ta j)`.

Establish `h2` using `hz.2.2.1 (Λ.ta j) (Λ.ph j)`. Rewrite `h1` using `[hc]`. Simplify using `only [hρ, map_inv, Λ.p_ta, Λ.p_ph, map_one, inv_one, one_mul, mul_one] at h1 h2`. Rewrite `h1` using `[h2]`. Establish `h3 : z (Λ.ta j) = mat x.ρ (T.sg j) * z (Λ.ta j) * mat x.ρ (T.sg j)⁻¹`.

Use `h1` as an intermediate fact. Rewrite `this` using `[add_comm (z (Λ.ta j))]`. Conclude with `add_left_cancel this`. Establish `hPZ : mat x.ρ (T.sg j) * z (Λ.ta j) = z (Λ.ta j) * mat x.ρ (T.sg j)` using `by conv_rhs => rw [h3]`. Rewrite using `[mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]`.

Conclude with `od_comm x.A n x.a (mat x.ρ (T.sg j)) (z (Λ.ta j)) (al j) (x.blk _) (hz.1 _) (hE j).1 (hE j).2 hPZ`. Take `⟨y, hy⟩` from `coc_ker l L Λ.G G0 Λ.h n x (Set.range Λ.ta) z (by rw [← Set.range_comp]; exact ker_oo l L G0 T Λ hP) (by`. Introduce and unpack `a ⟨j, rfl⟩`. Conclude with `⟨Λ.p_ta j, hzero j⟩)`. Use `hz`.

Establish `hzy : (fun g => y (Λ.h.p₀ g)) = z` using `funext hy`. Establish `hy' : y ∈ SelZ G0.frame x.t (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a)`. Rewrite using `[← Glob.Hom.sel_iff Λ.h, hzy]`. Conclude with `hz`. Take `⟨s, c, hsc⟩` from `k.gen y hy'`.

Use `⟨s, c, ?_⟩` and prove the remaining obligations. Establish `hb` using `(Glob.Hom.bd_iff Λ.h (x.ρX x.A) (Od x.A x.A n x.a) _).mpr hsc`. Use `show _ ∈ Bd Λ.G.frame (fun g => x.ρX x.A (Λ.h.p₀ g)) (Od x.A x.A n x.a)`. Use `hb using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`.

Simplify using `[hy]`.
-/
theorem UpperTheory.V.Pa.koszulThree_of_det :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (al : Fin T.q → Fin n → x.A), T.ProL → T.Eig x al → K3 Λ.h k := by
  intro l _ L G0 T Λ n x k al hP hE
  intro z hz
  have hρ : ∀ g, x.ρX x.A g = mat x.ρ g := by
    intro g
    ext i j
    simp [NP.ρX]
  have hzero : ∀ j, z (Λ.ta j) = 0 := by
    intro j
    have hc := Λ.comm j
    have h1 := hz.2.2.1 (Λ.ph j) (Λ.ta j)
    have h2 := hz.2.2.1 (Λ.ta j) (Λ.ph j)
    rw [hc] at h1
    simp only [hρ, map_inv, Λ.p_ta, Λ.p_ph, map_one, inv_one, one_mul, mul_one] at h1 h2
    rw [h2] at h1
    have h3 : z (Λ.ta j) = mat x.ρ (T.sg j) * z (Λ.ta j) * mat x.ρ (T.sg j)⁻¹ := by
      have := h1
      rw [add_comm (z (Λ.ta j))] at this
      exact add_left_cancel this
    have hPZ : mat x.ρ (T.sg j) * z (Λ.ta j) = z (Λ.ta j) * mat x.ρ (T.sg j) := by
      conv_rhs => rw [h3]
      rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
    exact od_comm x.A n x.a (mat x.ρ (T.sg j)) (z (Λ.ta j)) (al j) (x.blk _) (hz.1 _)
      (hE j).1 (hE j).2 hPZ
  obtain ⟨y, hy⟩ := coc_ker l L Λ.G G0 Λ.h n x (Set.range Λ.ta) z
    (by rw [← Set.range_comp]; exact ker_oo l L G0 T Λ hP)
    (by
      rintro a ⟨j, rfl⟩
      exact ⟨Λ.p_ta j, hzero j⟩)
    hz
  have hzy : (fun g => y (Λ.h.p₀ g)) = z := funext hy
  have hy' : y ∈ SelZ G0.frame x.t (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a) := by
    rw [← Glob.Hom.sel_iff Λ.h, hzy]
    exact hz
  obtain ⟨s, c, hsc⟩ := k.gen y hy'
  refine ⟨s, c, ?_⟩
  have hb := (Glob.Hom.bd_iff Λ.h (x.ρX x.A) (Od x.A x.A n x.a) _).mpr hsc
  show _ ∈ Bd Λ.G.frame (fun g => x.ρX x.A (Λ.h.p₀ g)) (Od x.A x.A n x.a)
  convert hb using 1
  funext g
  simp [hy]
