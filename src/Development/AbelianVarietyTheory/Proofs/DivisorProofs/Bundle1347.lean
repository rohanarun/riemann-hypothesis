module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1311
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0011
public import GroundTheory.GlobalFields.SemilocalAlgebras.Finite
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0778
public import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianDimensionBound
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

namespace GlobalTheory

theorem finrank_le_card_of_isotropic_prod_pi (F : Type) [Field F] (κ : Type) [Fintype κ]
    (L : Submodule F ((κ → F) × (κ → F)))
    (hL : ∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) :
    Module.finrank F L ≤ Fintype.card κ := by
  classical
  let ω : ((κ → F) × (κ → F)) →ₗ[F] Module.Dual F ((κ → F) × (κ → F)) :=
    LinearMap.mk₂ F (fun b a => a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2)
      (by intro b b' a; simp [dotProduct_add, add_dotProduct]; ring)
      (by intro c b a; simp [dotProduct_smul, smul_dotProduct]; ring)
      (by intro b a a'; simp [dotProduct_add, add_dotProduct]; ring)
      (by intro c b a; simp [dotProduct_smul, smul_dotProduct]; ring)
  have hω : ∀ b a, ω b a = a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2 := fun b a => rfl
  have hinj : Function.Injective ω := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    have h1 : ∀ i, b.2 i = 0 := by
      intro i
      have := congrArg (fun f => f (Pi.single i 1, 0)) hb
      simpa [hω, single_dotProduct] using this
    have h2 : ∀ i, b.1 i = 0 := by
      intro i
      have := congrArg (fun f => f (0, Pi.single i 1)) hb
      simpa [hω, dotProduct_single] using this
    exact Prod.ext (funext h2) (funext h1)
  let g : L →ₗ[F] L.dualAnnihilator :=
    ((ω.domRestrict L).codRestrict L.dualAnnihilator (by
      intro b
      rw [Submodule.mem_dualAnnihilator]
      intro a ha
      simp only [LinearMap.domRestrict_apply, hω]
      rw [hL a ha b b.2, sub_self]))
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply hinj
    have := congrArg Subtype.val hxy
    simpa [g] using this
  have h1 := LinearMap.finrank_le_finrank_of_injective hg
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq L
  have h3 : Module.finrank F ((κ → F) × (κ → F)) = 2 * Fintype.card κ := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]; ring
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LandherrStandardDefiniteHermitianCmField
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LandherrStd

open GroundTheory.Global.SemiLocal
open scoped GroundTheory.Global.SemiLocal

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem finrank_pos (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (u : HeightOneSpectrum (𝓞 E))
    [u.asIdeal.LiesOver v.asIdeal] :
    0 < Module.finrank (v.adicCompletion (maximalRealSubfield E)) (u.adicCompletion E) := by
  rw [finrank_eq_ramificationIdx_mul_inertiaDeg E v u]
  exact Nat.mul_pos (Ideal.ramificationIdx_pos (R := _) u.asIdeal) (Ideal.inertiaDeg_pos _ _)

theorem det_map' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) : (M.map f).det = f M.det :=
  (RingHom.map_det f M).symm

theorem exists_sq_sub_mul_sq (hU : Unr E) (θ : E) (hθ0 : θ ≠ 0) (hθ : IsCMField.complexConj E θ = -θ)
    (d : maximalRealSubfield E) (hd : (d : E) = θ * θ) (a : maximalRealSubfield E)
    (hloc : ∀ w : Pl E, ¬ IsSplitAt w → ∃ z : w.adicCompletion E,
      algebraMap E (w.adicCompletion E) (a : E) = cj w z * z)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    ∃ x y : v.adicCompletion (maximalRealSubfield E),
      algebraMap _ (v.adicCompletion (maximalRealSubfield E)) a =
        x ^ 2 - algebraMap _ (v.adicCompletion (maximalRealSubfield E)) d * y ^ 2 := by
  set Fv := v.adicCompletion (maximalRealSubfield E)
  haveI : CharZero Fv :=
    charZero_of_injective_algebraMap (algebraMap (maximalRealSubfield E) Fv).injective
  have hd0 : d ≠ 0 := fun h => mul_ne_zero hθ0 hθ0 (hd.symm.trans (by rw [h]; rfl))
  by_cases hsq : IsSquare (algebraMap _ Fv d)
  · exact GlobalTheory.Published.HasseNormSt.of_isSquare ((_root_.map_ne_zero _).2 hd0) hsq _
  obtain ⟨w, hw⟩ := (GlobalTheory.QNorm.places_over (maximalRealSubfield E) E).2.1 v
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw, HeightOneSpectrum.under_asIdeal]⟩
  set ι := completionMap v w with hιdef
  have hι : ∀ x : maximalRealSubfield E,
      ι (algebraMap _ Fv x) = algebraMap E (w.adicCompletion E) (x : E) := by
    intro x
    rw [hιdef, completionMap_algebraMap, IsScalarTower.algebraMap_apply (maximalRealSubfield E) E]
    rfl
  set t := algebraMap E (w.adicCompletion E) θ with htdef
  have ht2 : t * t = ι (algebraMap _ Fv d) := by rw [hι, hd, map_mul]
  have hnot : ∀ s : Fv, t ≠ ι s := by
    intro s hs
    apply hsq
    refine ⟨s, ι.injective ?_⟩
    rw [← ht2, map_mul, hs]
  have hsm : ∀ (s : Fv) (y : w.adicCompletion E), s • y = ι s * y := fun s y => Algebra.smul_def s y
  have hli : LinearIndependent Fv ![(1 : w.adicCompletion E), t] := by
    rw [LinearIndependent.pair_iff]
    intro s r h
    rw [hsm, hsm, mul_one] at h
    by_cases hr : r = 0
    · subst hr
      rw [map_zero, zero_mul, add_zero] at h
      exact ⟨ι.injective (by rw [h, map_zero]), rfl⟩
    · exfalso
      apply hnot (-s / r)
      have hr' : ι r ≠ 0 := (_root_.map_ne_zero ι).2 hr
      rw [map_div₀, map_neg]
      field_simp
      linear_combination h
  have hsum := sum_finrank_eq E v
  rw [Algebra.IsQuadraticExtension.finrank_eq_two] at hsum
  have hle : Module.finrank Fv (w.adicCompletion E) ≤ 2 := by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun u : PlacesOver E v =>
      Module.finrank Fv (u.1.adicCompletion E)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ ⟨w, inferInstance⟩)
  haveI : Module.Finite Fv (w.adicCompletion E) := Module.finite_of_finrank_pos (finrank_pos v w)
  have hge : 2 ≤ Module.finrank Fv (w.adicCompletion E) := by
    simpa using hli.fintype_card_le_finrank
  have h2 : Module.finrank Fv (w.adicCompletion E) = 2 := le_antisymm hle hge
  have hns : ¬ IsSplitAt w := by
    rintro ⟨u, hne, hu⟩
    haveI : u.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw, ← hu, HeightOneSpectrum.under_asIdeal]⟩
    have hpos := finrank_pos v u
    have hne' : (⟨u, inferInstance⟩ : PlacesOver E v) ≠ ⟨w, inferInstance⟩ :=
      fun h => hne (congrArg Subtype.val h)
    have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun u : PlacesOver E v =>
      Module.finrank Fv (u.1.adicCompletion E))
      (Finset.subset_univ {(⟨u, inferInstance⟩ : PlacesOver E v), ⟨w, inferInstance⟩})
      (fun _ _ _ => Nat.zero_le _)
    rw [Finset.sum_pair hne', hsum] at this
    have key : Module.finrank Fv (u.adicCompletion E) + Module.finrank Fv (w.adicCompletion E) ≤ 2 := this
    rw [h2] at key
    have hpos' : 0 < Module.finrank Fv (u.adicCompletion E) := hpos
    omega
  obtain ⟨z, hz⟩ := hloc w hns
  have hcc := ((GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hns).1
  have hcj : ∀ s : Fv, cj w (ι s) = ι s := by
    have h := (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield E) v).equalizer
      ((GlobalTheory.ConjAtPlace.main E hU w).1.comp (continuous_completionMap v w))
      (continuous_completionMap v w) (funext fun x => ?_)
    · exact fun s => congrFun h s
    · simp only [Function.comp_apply]
      rw [← hιdef, hι, hcc]
      congr 1
      exact (IsCMField.complexConj E).commutes x
  have hct : cj w t = -t := by rw [htdef, hcc, hθ, map_neg]
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hzb : z = ι (b.repr z 0) + ι (b.repr z 1) * t := by
    conv_lhs => rw [← b.sum_repr z, Fin.sum_univ_two]
    simp [b, hsm]
  obtain ⟨A, C, hAC⟩ : ∃ A C : Fv, z = ι A + ι C * t := ⟨_, _, hzb⟩
  refine ⟨A, C, ι.injective ?_⟩
  rw [hι, hz, hAC, map_add (f := _), map_mul, hcj, hcj, hct, map_sub, map_mul, map_pow, map_pow, ← ht2]
  ring

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ)
    (H : Matrix (Fin n) (Fin n) E), IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H →
    (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H.map τ = cT (starRingEnd ℂ) Q * Q) →
    (∀ w : Pl E, ¬ IsSplitAt w → ∃ g : Matrix (Fin n) (Fin n) (w.adicCompletion E),
      H.map (algebraMap E (w.adicCompletion E)) = cT (cj w) g * g) →
    ∃ h : GL (Fin n) E, H = cT (IsCMField.complexConj E).toRingEquiv.toRingHom h.val * h.val := by
  intro E _ _ _ hU n H hH hτ hw
  have hG' : ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (H a b) = H b a := fun a b => by
    have := congrFun (congrFun hH b) a
    simpa [cT, ReciprocityTheory.ChartRestriction.G.FD.cc] using this
  have hG : ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc ((1 : Matrix (Fin n) (Fin n) E) a b) =
      (1 : Matrix (Fin n) (Fin n) E) b a := by
    intro a b
    by_cases h : a = b
    · subst h
      simp [ReciprocityTheory.ChartRestriction.G.FD.cc]
    · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h), ReciprocityTheory.ChartRestriction.G.FD.cc]
  have hs : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧
      H.map τ = Qᵀ * (1 : Matrix (Fin n) (Fin n) E).map τ * Q.map (starRingEnd ℂ) := by
    intro τ
    obtain ⟨Q, hQ, hQe⟩ := hτ τ
    refine ⟨Q.map (starRingEnd ℂ), ?_, ?_⟩
    · rw [det_map']
      exact (_root_.map_ne_zero _).2 hQ
    · have h1 : (Q.map (starRingEnd ℂ)).map (starRingEnd ℂ) = Q := by
        ext i j
        simp
      rw [hQe, Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.mul_one, h1]
      rfl
  have hd : H.det ≠ 0 := by
    obtain ⟨Q, hQ, hQe⟩ := hτ (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
    intro h0
    have h1 := congrArg Matrix.det hQe
    rw [det_map', h0, map_zero, Matrix.det_mul] at h1
    have h2 : (cT (starRingEnd ℂ) Q).det = starRingEnd ℂ Q.det := by
      unfold cT
      rw [Matrix.det_transpose, det_map']
    rw [h2] at h1
    exact mul_ne_zero ((_root_.map_ne_zero _).2 hQ) hQ h1.symm
  have hd1 : (1 : Matrix (Fin n) (Fin n) E).det ≠ 0 := by simp
  obtain ⟨P, hP, hPe⟩ : ∃ P : Matrix (Fin n) (Fin n) E, P.det ≠ 0 ∧
      H = Pᵀ * 1 * P.map ReciprocityTheory.ChartRestriction.G.FD.cc := by
    refine GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt E n 1 H hG hG' hd1 hd hs ?_
    have hm : (1 : Matrix (Fin n) (Fin n) E).det / H.det ∈ maximalRealSubfield E := by
      rw [← IsCMField.complexConj_eq_self_iff, map_div₀]
      exact congrArg₂ (· / ·) (GlobalTheory.Published.cc_det_of_herm hG) (GlobalTheory.Published.cc_det_of_herm hG')
    let a : maximalRealSubfield E := ⟨_, hm⟩
    obtain ⟨θ, h0, hθ⟩ := GlobalTheory.Published.exists_cc_eq_neg E
    obtain ⟨d, hdθ⟩ := GlobalTheory.Published.exists_sq_real hθ
    have hd0 : d ≠ 0 := fun h => mul_ne_zero h0 h0 (hdθ.symm.trans (congrArg Subtype.val h))
    have ha0 : a ≠ 0 := fun h => div_ne_zero hd1 hd (congrArg Subtype.val h)
    have hloc : ∀ w : Pl E, ¬ IsSplitAt w → ∃ z : w.adicCompletion E,
        algebraMap E (w.adicCompletion E) (a : E) = cj w z * z := by
      intro w hns
      obtain ⟨g, hg⟩ := hw w hns
      have h1 := congrArg Matrix.det hg
      rw [det_map', Matrix.det_mul] at h1
      have h2 : (cT (cj w) g).det = cj w g.det := by
        unfold cT
        rw [Matrix.det_transpose, det_map']
      rw [h2] at h1
      refine ⟨g.det⁻¹, ?_⟩
      change algebraMap E (w.adicCompletion E) ((1 : Matrix (Fin n) (Fin n) E).det / H.det) = _
      rw [Matrix.det_one, one_div, map_inv₀, h1, map_inv₀, mul_inv]
    obtain ⟨x, y, hxy⟩ := GlobalTheory.QNorm.hasseNormSt (maximalRealSubfield E) d a hd0 ha0
      (fun ρ => by
        let τ := ComplexEmbedding.lift E (Complex.ofRealHom.comp ρ)
        have h1 : τ (a : E) = (Complex.ofRealHom.comp ρ) a :=
          ComplexEmbedding.lift_algebraMap_apply E _ a
        have h2 : 0 < (τ (a : E)).re := GlobalTheory.Published.Landherr.re_det_div_pos hd1 τ (hs τ)
        rw [h1] at h2
        exact ⟨√(ρ a), 0, by rw [Real.sq_sqrt (le_of_lt (by simpa using h2))]; ring⟩)
      (fun v => exists_sq_sub_mul_sq hU θ h0 hθ d hdθ a hloc v)
    refine ⟨x + y * θ, ?_⟩
    have h1 := congrArg (Subtype.val : maximalRealSubfield E → E) hxy
    have h2 : IsCMField.complexConj E θ = -θ := hθ
    simp [a, hdθ] at h1
    simp only [Matrix.det_one, one_div, ReciprocityTheory.ChartRestriction.G.FD.cc, map_add (f := _), map_mul,
      IsCMField.complexConj_apply_eq_self, h2]
    linear_combination h1
  have hPc : (P.map ReciprocityTheory.ChartRestriction.G.FD.cc).det ≠ 0 := by
    rw [show (P.map ReciprocityTheory.ChartRestriction.G.FD.cc) = P.map (IsCMField.complexConj E).toRingEquiv.toRingHom from rfl,
      det_map']
    exact (_root_.map_ne_zero _).2 hP
  let u : GL (Fin n) E := ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hPc)).unit
  refine ⟨u, ?_⟩
  have hu : (u : Matrix (Fin n) (Fin n) E) = P.map ReciprocityTheory.ChartRestriction.G.FD.cc := rfl
  rw [hu, hPe, Matrix.mul_one]
  congr 1
  ext i j
  simp [cT, ReciprocityTheory.ChartRestriction.G.FD.cc]

end GlobalTheory.LandherrStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeApproximationUpwardIdele
section
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped ContDiff

namespace GlobalTheory.SiegelSet

theorem isRealLine_add : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (γ : ℝ → GAd σ J), IsRealLine σ J γ →
      ∀ s t, γ (s + t) = γ s * γ t := by
  intro F E _ _ _ _ _ σ hCM n J γ hγ s t
  obtain ⟨w, τ, Z, -, hγ⟩ := hγ
  obtain ⟨y1, e1, f1⟩ := hγ (s + t)
  obtain ⟨y2, e2, f2⟩ := hγ s
  obtain ⟨y3, e3, f3⟩ := hγ t
  rw [e1, e2, e3, ← map_mul]
  congr 1
  apply (archEquiv J hCM τ).injective
  apply Subtype.ext
  apply Units.ext
  rw [← GlobalTheory.Orb.archMat_eq_archEquiv, ← GlobalTheory.Orb.archMat_eq_archEquiv, map_mul, f1, f2, f3, add_smul]
  exact Matrix.exp_add_of_commute _ _ ((Commute.refl Z).smul_left s |>.smul_right t)

end GlobalTheory.SiegelSet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureChangeFramedGeometricPointUnique
section
noncomputable section

namespace GlobalTheory.LevelFree

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LevPull

open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}

theorem eta_injective (Xo : Moduli Dw l) {k : Type} [Field k] [IsAlgClosed k] (x : Sp k ⟶ Xo.X) (β : KA l →+* k)
    (hx : x ≫ Xo.s = spMap β) (a : Dw.La) (h : toUnit (Over.mk x) ≫ Xo.univ.eta a = 1) :
    a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
  obtain ⟨-, I, -, -, hI⟩ := Xo.univ.geom k x β hx
  have htop : l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La) = ⊤ := by
    rw [← Submodule.sup_smul, l.coprime, Submodule.top_smul]
  have ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La) := by
    rw [htop]; trivial
  obtain ⟨a₂, h₂, a₁, h₁, rfl⟩ := Submodule.mem_sup.1 ha
  have e : toUnit (Over.mk x) ≫ Xo.univ.eta (a₂ + a₁) = toUnit (Over.mk x) ≫ Xo.univ.eta a₁ := by
    rw [Xo.univ.eta_add, Xo.univ.eta_ker a₂ h₂, _root_.one_mul]
  have e₁ : I.ev l.M a₁ = 1 := (hI a₁ h₁).symm.trans (e.symm.trans h)
  have hM : 0 < l.M := by have := l.three_le; omega
  obtain ⟨b, rfl⟩ := (I.ker l.M hM a₁).1 e₁
  have hMm : (l.M : 𝓞 E) ∈ l.Mb := by
    have : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    have hle : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb := Ideal.mul_le_left
    exact hle this
  refine Submodule.add_mem _ h₂ ?_
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul hMm trivial

section Bridge

abbrev fib {X Y : Scheme.{0}} (G : Over X) (x : Y ⟶ X) : Over Y := (Over.pullback x).obj G

variable {X : Scheme.{0}} {G : Over X} [GrpObj G]

def pushAt {ρ : X ⟶ X} {F : G.left ⟶ G.left} (h : IsGrpPullback G G ρ F) (T : Over X) (c : T.left ⟶ X)
    (e : T.hom ≫ ρ = c) : (T ⟶ G) →* (Over.mk c ⟶ G) :=
  MonoidHom.mk' (fun u => Over.homMk (u.left ≫ F) (by
      subst e
      show (u.left ≫ F) ≫ G.hom = T.hom ≫ ρ
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w u])) (fun a b => by
    subst e
    exact Over.OverMorphism.ext (h.2 T a b _ _ rfl rfl).symm)

theorem one_left_congr {T : Scheme.{0}} {c c' : T ⟶ X} (h : c = c') :
    (1 : Over.mk c ⟶ G).left = (1 : Over.mk c' ⟶ G).left := by
  subst h; rfl

end Bridge

theorem sections_eq {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) [IsProper G.hom]
    {ρ ρ' : X ⟶ X} {F F' : G.left ⟶ G.left} (h : IsGrpPullback G G ρ F) (h' : IsGrpPullback G G ρ' F')
    {k : Type} [Field k] [CharZero k] (x : Sp k ⟶ X) (hx : x ≫ ρ = x ≫ ρ')
    (ht : ∀ w : overAt x (DualNumber k) ⟶ G, smT x 0 w = 1 → w.left ≫ F = w.left ≫ F')
    (s : Over.mk x ⟶ G) : s.left ≫ F = s.left ≫ F' := by
  have pA : IsGrpPullback (fib G x) G x (pullback.fst G.hom x) := isGrpPullback_pullback G x
  have pB : IsGrpPullback (fib G (x ≫ ρ)) G (x ≫ ρ) (pullback.fst G.hom (x ≫ ρ)) := isGrpPullback_pullback G (x ≫ ρ)
  have c₁ : IsGrpPullback (fib G x) G (x ≫ ρ) (pullback.fst G.hom x ≫ F) := IsGrpPullback.comp pA h
  have c₂ : IsGrpPullback (fib G x) G (x ≫ ρ) (pullback.fst G.hom x ≫ F') := hx ▸ IsGrpPullback.comp pA h'
  let f : fib G x ⟶ fib G (x ≫ ρ) := Over.homMk (pullback.lift (pullback.fst G.hom x ≫ F) (pullback.snd G.hom x) c₁.1.w) (pullback.lift_snd _ _ _)
  let f' : fib G x ⟶ fib G (x ≫ ρ) := Over.homMk (pullback.lift (pullback.fst G.hom x ≫ F') (pullback.snd G.hom x) c₂.1.w) (pullback.lift_snd _ _ _)
  have ef : f.left ≫ pullback.fst G.hom (x ≫ ρ) = pullback.fst G.hom x ≫ F := pullback.lift_fst _ _ _
  have ef' : f'.left ≫ pullback.fst G.hom (x ≫ ρ) = pullback.fst G.hom x ≫ F' := pullback.lift_fst _ _ _
  haveI : IsMonHom f := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback c₁ pB (𝟙 G) f (by simpa using ef)
  haveI : IsMonHom f' := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback c₂ pB (𝟙 G) f' (by simpa using ef')
  have hA : IsAbelianScheme (fib G x) := by
    haveI : IsProper (fib G x).hom := inferInstanceAs (IsProper (pullback.snd G.hom x))
    exact AbelianSchemeGerms.isAbelianScheme_of_proper _ (IsSemiAbelian.pullback x G hG)
  have hB : IsAbelianScheme (fib G (x ≫ ρ)) := by
    haveI : IsProper (fib G (x ≫ ρ)).hom := inferInstanceAs (IsProper (pullback.snd G.hom (x ≫ ρ)))
    exact AbelianSchemeGerms.isAbelianScheme_of_proper _ (IsSemiAbelian.pullback (x ≫ ρ) G hG)
  haveI : IsCommMonObj (fib G x) := hA.comm
  haveI : IsCommMonObj (fib G (x ≫ ρ)) := hB.comm
  have key : f = f' := by
    refine _root_.GlobalTheory.LieFaithful.hom_eq_of_tangent_eq k _ _ hA hB f f' fun v hv => ?_
    let w : overAt x (DualNumber k) ⟶ G := Over.homMk (v.left ≫ pullback.fst G.hom x) (by
      have e := Over.w v
      show (v.left ≫ pullback.fst G.hom x) ≫ G.hom = spMap (algebraMap k (DualNumber k)) ≫ x
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      have e' : v.left ≫ pullback.snd G.hom x = spMap (algebraMap k (DualNumber k)) ≫ 𝟙 (Sp k) := e
      rw [e', Category.comp_id])
    have hw : smT x 0 w = 1 := by
      apply Over.OverMorphism.ext
      have e₁ : (smT x 0 w).left = (smT (𝟙 (Sp k)) 0 v).left ≫ pullback.fst G.hom x := by
        simp only [smT_left, w, Over.homMk_left, Category.assoc]
      rw [e₁, hv]
      have e₂ := congrArg (fun z => z.left) (map_one (pushHom pA (overAt (𝟙 (Sp k)) (DualNumber k))))
      refine e₂.trans (one_left_congr ?_)
      simp
    have e := ht w hw
    apply Over.OverMorphism.ext
    refine pB.1.hom_ext ?_ ?_
    · simp only [Over.comp_left, Category.assoc]
      rw [ef, ef']
      simpa [w] using e
    · rw [Over.w, Over.w]
  let a : Over.mk (𝟙 (Sp k)) ⟶ fib G x := Over.homMk (pullback.lift s.left (𝟙 _) (by simpa using Over.w s)) (pullback.lift_snd _ _ _)
  have ea : a.left ≫ pullback.fst G.hom x = s.left := pullback.lift_fst _ _ _
  have e1 : a.left ≫ f.left ≫ pullback.fst G.hom (x ≫ ρ) = s.left ≫ F := by
    rw [ef, ← Category.assoc, ea]
  have e2 : a.left ≫ f'.left ≫ pullback.fst G.hom (x ≫ ρ) = s.left ≫ F' := by
    rw [ef', ← Category.assoc, ea]
  rw [← e1, ← e2, key]

theorem move_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La), IsLift lift → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y y' : FrPt Xo c k) (g g' : Gam Dw l), levR (lift g, LinearMap.id) y y' → levR (lift g', LinearMap.id) y y' → g = g' := by
  intro E _ _ _ H Dw l Xo c _ _ lift hl k _ _ _ y y' g g' h h'
  obtain ⟨ρ, ν, -, hm, hf⟩ := h
  obtain ⟨ρ', ν', -, hm', hf'⟩ := h'
  haveI : CharZero k := charZero_of_injective_algebraMap (algebraMap c.F k).injective
  haveI : IsProper Xo.univ.t.G.hom := Xo.univ.proper
  have hx : y.x ≫ ρ = y.x ≫ ρ' := hf.1.symm.trans hf'.1
  have hu : ∀ τ i, y.u τ i ≫ ν.φ = y.u τ i ≫ ν'.φ := fun τ i => (hf.2.1 τ i).symm.trans (hf'.2.1 τ i)
  have ht : ∀ w : overAt y.x (DualNumber k) ⟶ Xo.univ.t.G, smT y.x 0 w = 1 → w.left ≫ ν.φ = w.left ≫ ν'.φ := by
    intro w hw
    have hT : IsTanAt y.x w.left := isTanAtG_of (t := Xo.univ.t) w hw
    obtain ⟨a, ⟨u, hu1, hu2⟩, -⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.FrTan.frTanBasis_holds Xo c k y w.left hT
    let P := pushAt ν.cart (overAt y.x (DualNumber k)) ((overAt y.x (DualNumber k)).hom ≫ ρ) rfl
    let P' := pushAt ν'.cart (overAt y.x (DualNumber k)) ((overAt y.x (DualNumber k)).hom ≫ ρ)
      (by simp only [Over.mk_hom, Category.assoc, hx])
    have e₁ : ∀ i, P (u i) = P' (u i) := fun i => by
      apply Over.OverMorphism.ext
      show (u i).left ≫ ν.φ = (u i).left ≫ ν'.φ
      rw [hu1, Category.assoc, Category.assoc, hu]
    have e₂ : P (List.ofFn u).prod = P' (List.ofFn u).prod := by
      rw [map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
      congr 2
      exact funext e₁
    have e₃ := congrArg (fun z => z.left) e₂
    have e₄ : ((List.ofFn u).prod).left ≫ ν.φ = ((List.ofFn u).prod).left ≫ ν'.φ := e₃
    rw [hu2] at e₄
    exact e₄
  have hs := sections_eq Xo.univ.t.semi ν.cart ν'.cart y.x hx ht
  have tl : (toUnit (Over.mk y.x)).left = y.x := by simpa using Over.w (toUnit (Over.mk y.x))
  have hη : ∀ a, toUnit (Over.mk y.x) ≫ Xo.univ.eta (lift g a) = toUnit (Over.mk y.x) ≫ Xo.univ.eta (lift g' a) := by
    intro a
    have e₁ : (toUnit (Over.mk y.x) ≫ Xo.univ.eta (lift g a)).left ≫ ν.φ = y.x ≫ ρ ≫ (Xo.univ.eta a).left := by
      rw [Over.comp_left, tl, Category.assoc, ← hm.2.1 a]
    have e₂ : (toUnit (Over.mk y.x) ≫ Xo.univ.eta (lift g' a)).left ≫ ν'.φ = y.x ≫ ρ' ≫ (Xo.univ.eta a).left := by
      rw [Over.comp_left, tl, Category.assoc, ← hm'.2.1 a]
    apply Over.OverMorphism.ext
    refine ν.cart.1.hom_ext ?_ ?_
    · rw [e₁, hs, e₂, ← Category.assoc, ← Category.assoc, hx]
    · rw [Over.w, Over.w]
  have hz : ∀ a, lift g a - lift g' a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
    intro a
    refine eta_injective Xo y.x ((algebraMap c.F k).comp (IntermediateField.inclusion c.le).toRingHom) y.x_over _ ?_
    have e : toUnit (Over.mk y.x) ≫ Xo.univ.eta (lift g a) =
        (toUnit (Over.mk y.x) ≫ Xo.univ.eta (lift g a - lift g' a)) * (toUnit (Over.mk y.x) ≫ Xo.univ.eta (lift g' a)) := by
      rw [← MonObj.comp_mul, ← Xo.univ.eta_add, sub_add_cancel]
    rw [hη a] at e
    exact (mul_eq_right.1 e.symm)
  refine LinearEquiv.ext fun q => ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have e₁ := LinearMap.congr_fun (hl g) a
  have e₂ := LinearMap.congr_fun (hl g') a
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe] at e₁ e₂
  rw [← e₁, ← e₂]
  exact (Submodule.Quotient.eq _).2 (hz a)

end GlobalTheory.LevelFree
end
end

