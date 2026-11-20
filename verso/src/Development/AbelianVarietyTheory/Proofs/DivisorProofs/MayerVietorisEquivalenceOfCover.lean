import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMayerVietorisConnectingExactStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.MayerVietorisEqv

/- English proof (translation)
Introduce `R _ U V E U' V' E' f g f' g' p u v hu hv F hc hc' hU hV hW`. Take `⟨d, hex, hnat⟩` from `GlobalTheory.T.exists_mayerVietoris_connecting_exact R F`. Establish `hwf : pullback.map f g f' g' u v p hu hv ≫ pullback.fst f' g' = pullback.fst f g ≫ u` using `pullback.lift_fst _ _ _`. Establish `hwg : pullback.map f g f' g' u v p hu hv ≫ pullback.snd f' g' = pullback.snd f g ≫ v` using `pullback.lift_snd _ _ _`. Establish `cf : ∀ n x, pull R f F n (pull R p F n x) = pull R u F n (pull R f' F n x)`.

Introduce `n x`. Rewrite using `[← pull_comp, ← pull_comp, hu]`. Establish `cg : ∀ n x, pull R g F n (pull R p F n x) = pull R v F n (pull R g' F n x)`. Introduce `n x`. Rewrite using `[← pull_comp, ← pull_comp, hv]`.

Establish `cfst : ∀ n x, pull R (pullback.map f g f' g' u v p hu hv) F n (pull R (pullback.fst f' g') F n x) = pull R (pullback.fst f g) F n (pull R u F n x)`. Introduce `n x`. Rewrite using `[← pull_comp, ← pull_comp, hwf]`. Establish `csnd : ∀ n x, pull R (pullback.map f g f' g' u v p hu hv) F n (pull R (pullback.snd f' g') F n x) = pull R (pullback.snd f g) F n (pull R v F n x)`. Introduce `n x`.

Rewrite using `[← pull_comp, ← pull_comp, hwg]`. Establish `hcond : ∀ n x, pull R (pullback.fst f g) F n (pull R f F n x) = pull R (pullback.snd f g) F n (pull R g F n x)`. Introduce `n x`. Rewrite using `[← pull_comp, ← pull_comp, pullback.condition]`. Introduce `n`.

Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by ring⟩`. Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `y hy`. Establish `h1 : pull R f' F (m + 1) y = 0`.

Apply `(hU (m + 1)).1` to reduce the goal to its premises. Rewrite using `[← cf, hy, map_zero, map_zero]`. Establish `h2 : pull R g' F (m + 1) y = 0`. Apply `(hV (m + 1)).1` to reduce the goal to its premises. Rewrite using `[← cg, hy, map_zero, map_zero]`.

Take `⟨c, rfl⟩` from `((hex f' g' hc' m).2.2 y).1 ⟨h1, h2⟩`. Establish `hd : d f g hc m (pull R (pullback.map f g f' g' u v p hu hv) F m c) = 0`. Rewrite using `[← hnat f g f' g' p u v hu hv hc hc' m c]`. Conclude with `hy`. Take `⟨a, b, hab⟩` from `((hex f g hc m).2.1 _).1 hd`.

Take `⟨a', rfl⟩` from `(hU m).2 a`. Take `⟨b', rfl⟩` from `(hV m).2 b`. Establish `hc1 : c = pull R (pullback.fst f' g') F m a' - pull R (pullback.snd f' g') F m b'`. Apply `(hW m).1` to reduce the goal to its premises. Rewrite using `[hab, map_sub, cfst, csnd]`.

Conclude with `((hex f' g' hc' m).2.1 c).2 ⟨a', b', hc1⟩`. Introduce `z`. Take `⟨a', ha'⟩` from `(hU (m + 1)).2 (pull R f F (m + 1) z)`. Take `⟨b', hb'⟩` from `(hV (m + 1)).2 (pull R g F (m + 1) z)`. Establish `hab : pull R (pullback.fst f' g') F (m + 1) a' = pull R (pullback.snd f' g') F (m + 1) b'`.

Apply `(hW (m + 1)).1` to reduce the goal to its premises. Rewrite using `[cfst, csnd, ha', hb', hcond]`. Take `⟨y, hy1, hy2⟩` from `((hex f' g' hc' (m + 1)).1 a' b').1 hab`. Establish `k1 : pull R f F (m + 1) (z - pull R p F (m + 1) y) = 0`. Rewrite using `[map_sub, cf, hy1, ha', sub_self]`.

Establish `k2 : pull R g F (m + 1) (z - pull R p F (m + 1) y) = 0`. Rewrite using `[map_sub, cg, hy2, hb', sub_self]`. Take `⟨c, hc0⟩` from `((hex f g hc m).2.2 _).1 ⟨k1, k2⟩`. Take `⟨c', rfl⟩` from `(hW m).2 c`. Use `⟨y + d f' g' hc' m c', ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, hnat f g f' g' p u v hu hv hc hc' m c', hc0]`. Normalize the expressions using the abelian group laws.
-/
theorem a4 : GlobalTheory.EtC.A4 := by
  intro R _ U V E U' V' E' f g f' g' p u v hu hv F hc hc' hU hV hW
  obtain ⟨d, hex, hnat⟩ := GlobalTheory.T.exists_mayerVietoris_connecting_exact R F
  have hwf : pullback.map f g f' g' u v p hu hv ≫ pullback.fst f' g' = pullback.fst f g ≫ u := pullback.lift_fst _ _ _
  have hwg : pullback.map f g f' g' u v p hu hv ≫ pullback.snd f' g' = pullback.snd f g ≫ v := pullback.lift_snd _ _ _
  have cf : ∀ n x, pull R f F n (pull R p F n x) = pull R u F n (pull R f' F n x) := by
    intro n x; rw [← pull_comp, ← pull_comp, hu]
  have cg : ∀ n x, pull R g F n (pull R p F n x) = pull R v F n (pull R g' F n x) := by
    intro n x; rw [← pull_comp, ← pull_comp, hv]
  have cfst : ∀ n x, pull R (pullback.map f g f' g' u v p hu hv) F n (pull R (pullback.fst f' g') F n x) =
      pull R (pullback.fst f g) F n (pull R u F n x) := by
    intro n x; rw [← pull_comp, ← pull_comp, hwf]
  have csnd : ∀ n x, pull R (pullback.map f g f' g' u v p hu hv) F n (pull R (pullback.snd f' g') F n x) =
      pull R (pullback.snd f g) F n (pull R v F n x) := by
    intro n x; rw [← pull_comp, ← pull_comp, hwg]
  have hcond : ∀ n x, pull R (pullback.fst f g) F n (pull R f F n x) =
      pull R (pullback.snd f g) F n (pull R g F n x) := by
    intro n x; rw [← pull_comp, ← pull_comp, pullback.condition]
  intro n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    have h1 : pull R f' F (m + 1) y = 0 := by
      apply (hU (m + 1)).1
      rw [← cf, hy, map_zero, map_zero]
    have h2 : pull R g' F (m + 1) y = 0 := by
      apply (hV (m + 1)).1
      rw [← cg, hy, map_zero, map_zero]
    obtain ⟨c, rfl⟩ := ((hex f' g' hc' m).2.2 y).1 ⟨h1, h2⟩
    have hd : d f g hc m (pull R (pullback.map f g f' g' u v p hu hv) F m c) = 0 := by
      rw [← hnat f g f' g' p u v hu hv hc hc' m c]; exact hy
    obtain ⟨a, b, hab⟩ := ((hex f g hc m).2.1 _).1 hd
    obtain ⟨a', rfl⟩ := (hU m).2 a
    obtain ⟨b', rfl⟩ := (hV m).2 b
    have hc1 : c = pull R (pullback.fst f' g') F m a' - pull R (pullback.snd f' g') F m b' := by
      apply (hW m).1
      rw [hab, map_sub, cfst, csnd]
    exact ((hex f' g' hc' m).2.1 c).2 ⟨a', b', hc1⟩
  · intro z
    obtain ⟨a', ha'⟩ := (hU (m + 1)).2 (pull R f F (m + 1) z)
    obtain ⟨b', hb'⟩ := (hV (m + 1)).2 (pull R g F (m + 1) z)
    have hab : pull R (pullback.fst f' g') F (m + 1) a' = pull R (pullback.snd f' g') F (m + 1) b' := by
      apply (hW (m + 1)).1
      rw [cfst, csnd, ha', hb', hcond]
    obtain ⟨y, hy1, hy2⟩ := ((hex f' g' hc' (m + 1)).1 a' b').1 hab
    have k1 : pull R f F (m + 1) (z - pull R p F (m + 1) y) = 0 := by
      rw [map_sub, cf, hy1, ha', sub_self]
    have k2 : pull R g F (m + 1) (z - pull R p F (m + 1) y) = 0 := by
      rw [map_sub, cg, hy2, hb', sub_self]
    obtain ⟨c, hc0⟩ := ((hex f g hc m).2.2 _).1 ⟨k1, k2⟩
    obtain ⟨c', rfl⟩ := (hW m).2 c
    refine ⟨y + d f' g' hc' m c', ?_⟩
    rw [map_add, hnat f g f' g' p u v hu hv hc hc' m c', hc0]
    abel

end GlobalTheory.MayerVietorisEqv
