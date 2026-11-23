module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0535
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1865
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1492
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1028
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1800
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericRowCoefMemCoefAlgebraOfDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1887
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1890
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionOverFieldEqOfClosedPointImageEq
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory

theorem section_eq_of_point_eq : ∀ (K : Type) [Field K] (X : Scheme.{0}) (q : X ⟶ Sp K) (z z' : Sp K ⟶ X), z ≫ q = 𝟙 _ → z' ≫ q = 𝟙 _ → z (IsLocalRing.closedPoint K) = z' (IsLocalRing.closedPoint K) → z = z' := by
  intro K _ X q z z' hz hz' hpt
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective z
  obtain ⟨⟨p', ψ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective z'
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hz hz' hpt ⊢
  have e : p = p' := by
    have h1 := (Scheme.Hom.comp_apply _ _ _).symm.trans (hpt.trans (Scheme.Hom.comp_apply _ _ _))
    rwa [Scheme.fromSpecResidueField_apply, Scheme.fromSpecResidueField_apply] at h1
  subst e
  obtain ⟨χ, hχ⟩ := Spec.map_surjective (X.fromSpecResidueField p ≫ q)
  rw [Category.assoc, ← hχ, ← Spec.map_comp, ← Spec.map_id, Spec.map_inj] at hz hz'
  have hφ : ∀ c, φ.hom (χ.hom c) = c := fun c => congrArg (fun g => g.hom c) hz
  have hψ : ∀ c, ψ.hom (χ.hom c) = c := fun c => congrArg (fun g => g.hom c) hz'
  have hsurj : Function.Surjective χ.hom := by
    intro y
    refine ⟨φ.hom y, φ.hom.injective ?_⟩
    rw [hφ]
  have : φ = ψ := by
    ext y
    obtain ⟨c, rfl⟩ := hsurj y
    rw [hφ, hψ]
  rw [this]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueTangentLiftEqFirstJet
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
open Filter Topology

noncomputable section

namespace GlobalTheory.MBLow.EpsVal

open GlobalTheory.TangentOrigin

theorem valR_comp_eq {R : Type} [CommRing R] {X Y : Scheme.{0}} (x : Sp R ⟶ X) (s : X ⟶ Y) (U : X.Opens) (V : Y.Opens)
    (e : U ≤ s ⁻¹ᵁ V) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(Y, V)) :
    valR (x ≫ s) V a = evalPt x U h ((s.appLE V U e).hom a) := by
  have h' : ⊤ ≤ (x ≫ s) ⁻¹ᵁ V := fun p hp => e (h hp)
  unfold valR evalPt
  rw [dite_eq_left h', ← Scheme.Hom.appLE_comp_appLE x s V U ⊤ e h]
  rfl

def sec (A : Over (Sp ℂ)) : A ⟶ baseOver (Sp ℂ) ⊗ A :=
  lift (Over.homMk A.hom (by simp) : A ⟶ baseOver (Sp ℂ)) (𝟙 A)

theorem sec_snd (A : Over (Sp ℂ)) : (sec A).left ≫ (snd (baseOver (Sp ℂ)) A).left = 𝟙 A.left := by
  rw [← Over.comp_left, sec, lift_snd, Over.id_left]

theorem epsLift_eq {A : Over (Sp ℂ)} (v : epsR ℂ ⟶ A) : epsLift v = v.left ≫ (sec A).left := by
  rw [← Over.comp_left, sec, comp_lift, Category.comp_id, epsLift]
  congr 2
  ext
  simp

theorem ptSecT_eq {A : Over (Sp ℂ)} (z : baseOver (Sp ℂ) ⟶ A) :
    (ptSecT A z).left = z.left ≫ (sec A).left := by
  rw [← Over.comp_left, sec, comp_lift, Category.comp_id, ptSecT]
  congr 2
  ext
  simpa using (Over.w z).symm

theorem le_sec {A : Over (Sp ℂ)} (L : LB A.left) (k : ℤ) (i : L.ι) :
    L.U i ≤ (sec A).left ⁻¹ᵁ ((LPow A L k (baseOver (Sp ℂ))).U fun _ => i) := by
  intro p hp
  refine Set.mem_iInter.2 fun _ => ?_
  change ((sec A).left ≫ (snd (baseOver (Sp ℂ)) A).left) p ∈ L.U i
  rw [sec_snd]
  exact hp

theorem valR_epsLift : ∀ (g : ℕ) (P : PolAV (Sp ℂ)) (u : HolUnif P.A P.L g) (k : ℕ) (t : LB.Sec (LPow P.A P.L (k : ℤ) (baseOver (Sp ℂ)))) (f : (Fin g → ℂ) → ℂ) (v : epsR ℂ ⟶ P.A) (W : Fin g → ℂ) (i : P.L.ι), FnT u k t f → Differentiable ℂ f → IsTangent v → u.IsDiff W v → ⊤ ≤ (eSec P.A) ⁻¹ᵁ P.L.U i → valR (epsLift v) ((LPow P.A P.L (k : ℤ) (baseOver (Sp ℂ))).U fun _ => i) (t.f fun _ => i) = TrivSqZeroExt.inl (u.fr i 0 ^ k) * (TrivSqZeroExt.inl (f 0) + TrivSqZeroExt.inr (fderiv ℂ f 0 W + (k * fderiv ℂ (u.fr i) 0 W / u.fr i 0) * f 0)) := by
  intro g P u k t f v W i hf hd hv hW hi
  have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ P.L.U i := by
    rw [ex_zero_left]; exact hi
  have h : ⊤ ≤ v.left ⁻¹ᵁ P.L.U i := (tangent_mem_iff (u := u) hv _).2 h0
  set a := ((sec P.A).left.appLE _ _ (le_sec P.L (k : ℤ) i)).hom (t.f fun _ => i) with ha
  have hval : ∀ z (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i),
      evalPt (R := ℂ) (u.ex z).left (P.L.U i) hz a = f z * u.fr i z ^ k := by
    intro z hz
    have := hf i z hz
    rw [ptSecT_eq] at this
    exact (valR_comp_eq (R := ℂ) (u.ex z).left (sec P.A).left _ _ (le_sec P.L (k : ℤ) i) hz _).symm.trans this
  have hev : (fun z => valAt' (u.ex z).left (P.L.U i) a) =ᶠ[𝓝 0] fun z => f z * u.fr i z ^ k := by
    filter_upwards [eventually_mem u h0] with z hz
    rw [valAt'_eq_evalPt _ _ hz, hval z hz]
  have hfr : DifferentiableAt ℂ (u.fr i) 0 := (u.fr_hol i).differentiableAt (eventually_mem u h0)
  have hne : u.fr i 0 ≠ 0 := u.fr_ne i 0 h0
  have hD := ((hd 0).hasFDerivAt.mul (hfr.hasFDerivAt.pow k)).fderiv
  rw [epsLift_eq]
  refine (valR_comp_eq (R := DualNumber ℂ) v.left (sec P.A).left _ _ (le_sec P.L (k : ℤ) i) h _).trans ?_
  refine TrivSqZeroExt.ext ?_ ?_
  · refine (tangent_fst (u := u) hv h h0 a).trans ?_
    rw [hval 0 h0]
    simp [mul_comm]
  · refine (hW _ h a).trans ?_
    rw [hev.fderiv_eq]
    refine (congrArg (fun φ => φ W) hD).trans ?_
    rcases k with _ | k
    · simp
    · simp
      field_simp
      ring

end GlobalTheory.MBLow.EpsVal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianTripleMapIsOpenImmersionOpensRange
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem sabMap_isOpenImmersion_opensRange (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (j : X' ⟶ X) [IsOpenImmersion j] (m : SABMap t' t j) : ∃ _ : IsOpenImmersion m.φ, m.φ.opensRange = t.G.hom ⁻¹ᵁ j.opensRange := by
  have h : IsPullback m.φ t'.G.hom t.G.hom j := m.cart.1
  have hφ : m.φ = h.isoPullback.hom ≫ pullback.fst t.G.hom j := by simp
  have hi : IsOpenImmersion m.φ := by rw [hφ]; infer_instance
  refine ⟨hi, ?_⟩
  ext1
  have h1 : Set.range m.φ = Set.range (pullback.fst t.G.hom j) := by
    rw [hφ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr h.isoPullback.hom.surjective, Set.image_univ]
  simpa [h1] using Scheme.Pullback.range_fst t.G.hom j
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelRuleDiagonalDoubledSchroedingerModel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DiagSiegel

open MeasureTheory

theorem dblD_diagCols {R E : Type} [CommRing R] [CommRing E] [Algebra R E] [Invertible (2 : R)] (c : E →ₐ[R] E)
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {ξ : E} {JA : Matrix α α E}
    {JB : Matrix β β E} {κ : Type} [Fintype κ] (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ)
    (z : Matrix α β E) :
    (GlobalTheory.DblSchr.dblD c d).e (z * (GlobalTheory.WeilM.diagCols β : Matrix (β ⊕ β) β E)ᵀ) =
      (Sum.elim (d.e z).1 (d.e z).1, Sum.elim (d.e z).2 (-(d.e z).2)) := by
  have h : z * (GlobalTheory.WeilM.diagCols β : Matrix (β ⊕ β) β E)ᵀ = Matrix.fromCols z z := by
    simp [GlobalTheory.WeilM.diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols]
  rw [h]
  exact GlobalTheory.DblSchr.isDblCoord_dblD c d z z

end GlobalTheory.DiagSiegel

theorem GlobalTheory.DiagSiegel.siegelRule_ddr : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
          ∀ omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (GlobalTheory.DblSchr.JBd S JB)) →*
              Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.DblSchr.ddr co) ωd omd₀ →
          GlobalTheory.WeilM.SiegelRule (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) ψ ξ (incM D.host.F JA)
            (GlobalTheory.WeilM.dbl (incM D.host.F JB)) (GlobalTheory.DblSchr.dblD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co) χT
            (GlobalTheory.WeilM.diagCols (Fin S.rank)) (GlobalTheory.DblSchr.omdOf omd₀) := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hξ κ _ co hco ωd hωd omd₀ htr
  intro l hl hinv p t hpt φ hφ
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.Size.exists_isCovolOne (D := D) S T
  letI mκ : MeasurableSpace (κ → AF D.host.F) := borel _
  haveI : BorelSpace (κ → AF D.host.F) := ⟨rfl⟩
  let μ : MeasureTheory.Measure (κ → AF D.host.F) := MeasureTheory.Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  have hinv' : ∀ x y : κ → AF D.host.F, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ),
      l (GlobalTheory.WeilM.schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) = l Φ := by
    intro x y Φ hΦ
    have h1 := hinv (co.e.symm (x, y)) Φ hΦ
    rw [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.DiagSiegel.dblD_diagCols, LinearEquiv.apply_symm_apply] at h1
    exact h1
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.HostDiagUniq.eq_smul_diagInt D ψ hψ κ l hl hinv' μ hμ
  obtain ⟨c₂, hc₂0, hc₂⟩ := _root_.GlobalTheory.DiagSiegelUnfold.diag_theta_integral D ψ hψ S T JA JB ξ hJA hξ κ co hco ν 𝓕 hν μ hμ
  obtain ⟨hmem, hrule⟩ := _root_.GlobalTheory.DiagThetaRule.thetaDiagInt_omdOf D ψ hψ S T JA JB ξ hJA hξ κ co hco ν 𝓕 hν χS χT hS hT rS rT ωd hωd omd₀ htr p t hpt φ hφ
  rw [hc₂ _ hmem, hc₂ _ hφ] at hrule
  have e := mul_left_cancel₀ hc₂0 (hrule.trans (mul_left_comm _ _ _))
  show l (GlobalTheory.DblSchr.omdOf omd₀ p φ) = _
  refine (hc _ hmem).trans ?_
  refine (congrArg (c * ·) e).trans ?_
  refine (mul_left_comm _ _ _).trans ?_
  have h3 := hc _ hφ
  rw [h3]
  rfl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimpleSubquotientDualWeylEmbedsHighestWeight
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem GlobalTheory.HighWt.simpleSubquot_embeds : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (lam τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], IsSimpleModule (alg O N lam) Gm → SubQ O N lam ϖ Gm → ∃ mu : ι → ℕ → ℕ, (∀ τ, Antitone (res N (mu τ)) ∧ ∑ a : Fin N, mu τ a = ∑ a : Fin N, lam τ a ∧ (∀ a : Fin N, lam τ (N - 1) ≤ mu τ a ∧ mu τ a ≤ lam τ 0) ∧ ∃ (e : alg O N lam) (z : Gm), IsProj O N lam τ (res N (mu τ)) e ∧ e • z ≠ 0) ∧ Embeds O N lam mu ϖ Gm := by
  intro O _ _ _ _ N ι _ _ lam ϖ hϖ hlam Gm _ _ hs hsub
  classical
  haveI : Nontrivial Gm := IsSimpleModule.nontrivial (alg O N lam) Gm
  obtain ⟨w0, hw0⟩ := _root_.GlobalTheory.HighWt.exists_jointWt O N ι lam Gm inferInstance
  have hB := _root_.GlobalTheory.HighWt.jointWt_bounds O N ι lam hlam Gm
  let S : Set (ι → Fin N → ℕ) := {w | GlobalTheory.HighWt.JointWt O N lam Gm w}
  have hfin : S.Finite := by
    refine Set.Finite.subset (Set.Finite.pi (t := fun τ => Set.pi Set.univ fun _ : Fin N => Set.Iic (lam τ 0))
      fun τ => Set.Finite.pi fun _ => Set.finite_Iic _) ?_
    intro w hw
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Iic, true_implies]
    intro τ a
    exact ((hB w hw τ).2 a).2
  obtain ⟨w, hwS, hmax⟩ := hfin.toFinset.exists_max_image (GlobalTheory.HighWt.pot N) ⟨w0, hfin.mem_toFinset.2 hw0⟩
  rw [Set.Finite.mem_toFinset] at hwS
  have hmax' : ∀ w', GlobalTheory.HighWt.JointWt O N lam Gm w' → GlobalTheory.HighWt.pot N w' ≤ GlobalTheory.HighWt.pot N w :=
    fun w' h' => hmax w' (hfin.mem_toFinset.2 h')
  have hanti := _root_.GlobalTheory.HighWt.antitone_of_pot_max O N ι lam Gm w hwS hmax'
  refine ⟨GlobalTheory.HighWt.extW N w, fun τ => ?_, _root_.GlobalTheory.HighWtEmb.embeds_of_maxWeight O N ι lam ϖ hϖ hlam _root_.GlobalTheory.HighWt.baseChange_holds (_root_.GlobalTheory.HighWt.coefIn_of_domain O N ι lam) Gm hs hsub w hanti hwS hmax'⟩
  rw [GlobalTheory.HighWt.res_extW]
  refine ⟨hanti τ, ?_, ?_, ?_⟩
  · have := (hB w hwS τ).1
    simpa [GlobalTheory.HighWt.extW, Fin.is_lt] using this
  · intro a
    simpa [GlobalTheory.HighWt.extW, Fin.is_lt] using (hB w hwS τ).2 a
  · obtain ⟨a, ha, -⟩ := _root_.GlobalTheory.ExpFrame.exists_unique_isProj O N ι lam τ (w τ)
    obtain ⟨z, hz, hfix⟩ := hwS
    let e : alg O N lam := ⟨a, Algebra.subset_adjoin (Or.inr ⟨τ, w τ, ha⟩)⟩
    refine ⟨e, z, ha, ?_⟩
    rw [hfix τ e ha]
    exact hz

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitFibresLocalisedModelBaseChange
section
noncomputable section

namespace GlobalTheory.KeyUnitModels.SplitLoc

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open scoped CategoryTheory.Obj

theorem isIso_residueFieldMap {Z X : Scheme.{0}} (i : Z ⟶ X) [SurjectiveOnStalks i] (z : Z) :
    IsIso (i.residueFieldMap z) := by
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨RingHom.injective _, fun u => ?_⟩
  obtain ⟨u, rfl⟩ := Z.residue_surjective _ u
  obtain ⟨u, rfl⟩ := i.stalkMap_surjective _ u
  exact ⟨X.residue _ u, ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i _) u⟩

theorem split_of_pullback {Z X : Scheme.{0}} (i : Z ⟶ X) [SurjectiveOnStalks i] {G : Over X} {G' : Over Z} [GrpObj G]
    [GrpObj G'] {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G i φ) (z : Z)
    (h : ∃ (k : Type) (_ : Field k) (_ : Algebra (X.residueField (i z)) k),
      FiniteDimensional (X.residueField (i z)) k ∧ Algebra.IsSeparable (X.residueField (i z)) k ∧
      ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (i z)) k)) ≫ X.fromSpecResidueField (i z))).obj G)) :
    ∃ (k : Type) (_ : Field k) (_ : Algebra (Z.residueField z) k),
      FiniteDimensional (Z.residueField z) k ∧ Algebra.IsSeparable (Z.residueField z) k ∧
      ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) k)) ≫ Z.fromSpecResidueField z)).obj G') := by
  obtain ⟨k, _, _, hfin, hsep, S, hS⟩ := h
  have := isIso_residueFieldMap i z
  let e : X.residueField (i z) ≃+* Z.residueField z := (asIso (i.residueFieldMap z)).commRingCatIsoToRingEquiv
  let _ : Algebra (Z.residueField z) k := ((algebraMap (X.residueField (i z)) k).comp e.symm.toRingHom).toAlgebra
  have he : (algebraMap (Z.residueField z) k).comp (e : _ →+* _) =
      ((RingEquiv.refl k : k ≃+* k) : k →+* k).comp (algebraMap (X.residueField (i z)) k) :=
    RingHom.ext fun a => congrArg (algebraMap (X.residueField (i z)) k) (e.symm_apply_apply a)
  refine ⟨k, inferInstance, inferInstance, Module.Finite.of_equiv_equiv e (RingEquiv.refl k) he,
    Algebra.IsSeparable.of_equiv_equiv e (RingEquiv.refl k) he, S, ?_⟩
  have hc : i.residueFieldMap z ≫ CommRingCat.ofHom (algebraMap (Z.residueField z) k) =
      CommRingCat.ofHom (algebraMap (X.residueField (i z)) k) := CommRingCat.hom_ext he
  have key : (Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) k)) ≫ Z.fromSpecResidueField z) ≫ i =
      Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (i z)) k)) ≫ X.fromSpecResidueField (i z) := by
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← hc]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ X.fromSpecResidueField (i z)) (Spec.map_comp _ _).symm)
  obtain ⟨j, hj, -⟩ := grpPullback_iso (isGrpPullback_pullback G _)
    (((isGrpPullback_pullback G' _).comp hφ).congr key rfl)
  exact isGt_of_iso j hS

theorem locModel_splitFibres : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
    (O' : Type) [CommRing O'] (β' : O' →+* c.F) (b : O →+* O') (hb : β'.comp b = β) [IsPreimmersion (spMap b)]
    [Flat (spMap b)], Y.SplitFibres → (locModel Y b hb).SplitFibres := by
  intro E _ _ _ H D l Xo c O _ β Y O' _ β' b hb _ _ h x
  exact split_of_pullback (pullback.fst Y.s (spMap b)) (locMap Y b).cart x (h _)

end GlobalTheory.KeyUnitModels.SplitLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveSectionsModBaseIdealOfClosedImmersion
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem surj_mod_baseIdeal_of_isClosedImmersion : ∀ (R : Type) [CommRing R] (I : Ideal R) (X Z : Scheme.{0}) (φ : X ⟶ Z) (p : Z ⟶ Spec (CommRingCat.of R)), IsClosedImmersion (((baseIdeal p I).comap φ).subschemeι ≫ φ) → ∀ (V : Z.Opens) (hV : IsAffineOpen V), IsAffineOpen (φ ⁻¹ᵁ V) → Function.Surjective ((Ideal.Quotient.mk (((baseIdeal p I).ideal ⟨V, hV⟩).map (φ.app V).hom)).comp (φ.app V).hom) := by
  intro R _ I X Z φ p hg V hV hW
  set K := (baseIdeal p I).comap φ with hK
  have hKid : K.ideal ⟨φ ⁻¹ᵁ V, hW⟩ = ((baseIdeal p I).ideal ⟨V, hV⟩).map (φ.app V).hom := by
    rw [hK, GlobalTheory.Principalise.comapIdealAffine (baseIdeal p I) φ ⟨V, hV⟩ ⟨φ ⁻¹ᵁ V, hW⟩ le_rfl,
      Scheme.Hom.app_eq_appLE]
  intro q
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨b, hb⟩ := Scheme.Hom.app_surjective (K.subschemeι ≫ φ) V hV
    ((K.subschemeι.app (φ ⁻¹ᵁ V)).hom c)
  refine ⟨b, ?_⟩
  simp only [RingHom.comp_apply]
  rw [Ideal.Quotient.eq, ← hKid, ← Scheme.IdealSheafData.ker_subschemeι_app, RingHom.mem_ker, map_sub]
  rw [Scheme.Hom.comp_app] at hb
  rw [sub_eq_zero]
  exact hb

end GlobalTheory.FormalAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryInvariantStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_form_unitary_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (g : UA σ X.J) (h : UA σ W.J) (x u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) (mat g * x * (mat h)ᵀ) (mat g * u * (mat h)ᵀ) =
      symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) x u := by
  first | exact @GlobalTheory.SympInv.symp_act | exact GlobalTheory.SympInv.symp_act | (intros; apply GlobalTheory.SympInv.symp_act <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisMovesAlongSemiAbelianTripleMap
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SabTan

theorem tanBasis_sabMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (j : X' ⟶ X) (m : SABMap t' t j) (S T : Type) [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ X) (x' : Sp T ⟶ X'), x' ≫ j = spMap ψ ≫ x → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), (∀ i, IsTanAtG t x (v i)) → (∀ w, IsTanAtG t x w → ∃! cf : Fin n → S, IsCombAtG t x v cf w) → ∃ v' : Fin n → (Sp (DualNumber T) ⟶ t'.G.left), (∀ i, v' i ≫ m.φ = spMap (dualMap ψ) ≫ v i) ∧ (∀ i, IsTanAtG t' x' (v' i)) ∧ ∀ w, IsTanAtG t' x' w → ∃! cf : Fin n → T, IsCombAtG t' x' v' cf w := by
  intro E _ _ _ H X X' t t' j m S T _ _ ψ x x' hx n v hv hv'
  have := t.semi.comm
  have := t'.semi.comm
  obtain ⟨k₁, k₂⟩ := GlobalTheory.LocM.FrameBase.tanBasis_baseChange t ψ x n v hv hv'
  rw [← hx] at k₁ k₂
  have h₁ := isGrpPullback_pullback t'.G x'
  have hc := h₁.comp m.cart
  obtain ⟨a, b⟩ := GlobalTheory.LocM.FrameBase.lieBasis_iff t (x' ≫ j) _ _ hc
  obtain ⟨-, b'⟩ := GlobalTheory.LocM.FrameBase.lieBasis_iff t' x' _ _ h₁
  choose u hu using fun i => a _ (k₁ i)
  have hu' : ∀ i, (u i).left ≫ pullback.fst t'.G.hom x' ≫ m.φ = spMap (dualMap ψ) ≫ v i := hu
  have hb := (b n u).2 ⟨fun i => by rw [hu']; exact k₁ i, by rw [funext hu']; exact k₂⟩
  obtain ⟨c₁, c₂⟩ := (b' n u).1 hb
  exact ⟨fun i => (u i).left ≫ pullback.fst t'.G.hom x', fun i => by rw [Category.assoc]; exact hu' i, c₁, c₂⟩

end GlobalTheory.SabTan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsDominantLastEntryOneDegreeStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaExponents_dominant_lastEntry_one_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (u : Weight Dw) (n : ℕ) (b : ℝ), 1 ≤ Dw.p → Even n → (∀ τ, Antitone (u τ)) → (∀ τ (i j : Fin (Dw.p + Dw.q)), (i : ℕ) + 1 = Dw.p → (j : ℕ) = Dw.p → (n : ℤ) + 1 ≤ u τ i - u τ j) → (∀ τ i, |(u τ i : ℝ)| ≤ b) → Dom (thA Dw u n) n ∧ wtZ (thA Dw u n) n = wtOf Dw (u + parWt Dw (shift Dw u n)) ((n / 2 : ℕ) : ℤ) ∧ LastPos Dw (thA Dw u n) ∧ (∀ x, (thA Dw u n x : ℝ) ≤ 2 * b + 1) ∧ (DF Dw (thA Dw u n) : ℝ) ≤ (Module.finrank ℚ E / 2 : ℕ) * (Dw.p + Dw.q : ℕ) * (2 * b + 1) := by
  first | exact @GlobalTheory.RefSum.thA_dominant_lastPos_degree | exact GlobalTheory.RefSum.thA_dominant_lastPos_degree | (intros; apply GlobalTheory.RefSum.thA_dominant_lastPos_degree <;> assumption)
end

