module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2832
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2056
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2399
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2380
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RegularOfBoundedAtPadicAlgClPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullFEPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2819
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0582
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightsTopGrid
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1594
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1606
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.PieriBlockIdeals.Bundle0003
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTotalExponentTopWeightBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2812
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2827
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsToSemiAbelianOfLocalGroups
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGroupRangeUnionClosedFibres

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMinimalPsiCoordinateAssociatedFourierPower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.QUnit

theorem FF_mem {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : S.J × (T → ZMod ((S.r * S.N) ^ 2))) : S.FF T c k ∈ S.R := by
  unfold ThetaSys.FF
  refine finsum_induction (fun v => v ∈ S.R) (zero_mem _) (fun _ _ => add_mem) fun t => ?_
  exact mul_mem (Subalgebra.algebraMap_mem _ _) (sum_mem fun i _ => mul_mem (Subalgebra.algebraMap_mem _ _) (S.ev_mem _ _))

theorem main : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ α₀ : D.toPre.X, ∃ mu : D.toPre.X, CongMod S.N mu α₀ ∧ (∀ α, CongMod S.N α α₀ → ∀ r s, PsiCoord D.toPre mu r → PsiCoord D.toPre α s → r ∣ s) ∧ ∃ (e : Ω) (a : M.Z.presheaf.stalk x), e ≠ 0 ∧ (∃ (T₀ : AddSubgroup S.Gam) (c' : T₀ →+ ZMod S.N) (κ : S.J × (T₀ → ZMod ((S.r * S.N) ^ 2))) (x₀ : S.Gam), S.IsoFree T₀ ∧ e = S.FF T₀ c' κ / S.th x₀) ∧ M.stalkHom x a = e ^ S.N ∧ ∀ r, PsiCoord D.toPre mu r → Associated (j a) r := by
  intro o' Ω _ _ _ _ S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R _ _ _ j hB hj G _ _ gm hpb D A U hLB hPsi α₀
  obtain ⟨hiso, hc⟩ := _root_.GlobalTheory.Poinc.CNorm.main o' Ω S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R j hB hj G gm hpb D A U hLB hPsi
  obtain ⟨c', hc'⟩ := hc α₀
  have hO := hAdm.1
  obtain ⟨x₀, hx₀⟩ := hO.div x
  have hRU : ∀ v ∈ S.R, v ∈ M.ringOn (U₀ : Set M.Z) := fun v hv => hO.le hv
  have hext : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ x y →
      ∃ ev : R →+* OO p, IsLocalHom ev ∧ spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y := by
    intro p _ y hy
    obtain ⟨V, _, _, _, ev₀, i, -, hl₀, hli, -, hev, -⟩ := GlobalTheory.ClassicalPt.extend_completion o' Ω M x R j hj p y hy.1
    haveI := hl₀
    haveI := hli
    exact ⟨i.comp ev₀, RingHom.isLocalHom_comp _ _, hev⟩
  obtain ⟨p₁, hp₁, y₁, hy₁⟩ := GlobalTheory.Poinc.exists_cen_main o' Ω M x hx U₀ hO.ne
  obtain ⟨ev₁, hl₁, hev₁⟩ := hext p₁ y₁ hy₁
  have hN0 : S.N ≠ 0 := by have := S.N_ge; omega
  have hFFne : S.FF (S.TT M x) c' ≠ 0 := by
    intro h0
    obtain ⟨hlow, κ₂, hup⟩ := hc' p₁ y₁ ev₁ hy₁ hev₁ x₀ hx₀
    obtain ⟨α, s, hα, hs, -⟩ := hlow κ₂
    have h1 := hup α s hα hs
    rw [show S.FF (S.TT M x) c' κ₂ = 0 from congrFun h0 κ₂, zero_div, RatModel.val_zero, norm_zero,
      zero_pow hN0] at h1
    exact _root_.GlobalTheory.Poinc.CoordNe.coord_ne_zero o' Ω S ρ M U₀ EE FinalForm hO x R j D hPsi p₁ y₁ ev₁ hy₁ hev₁ α s hs (norm_le_zero_iff.1 h1)
  obtain ⟨κ₁, hκ₁⟩ := hAdm.2 (S.TT M x) c' hiso hFFne x
  have he0 : S.FF (S.TT M x) c' κ₁ / S.th x₀ ≠ 0 := div_ne_zero hκ₁.1 hx₀.1
  have heU : S.FF (S.TT M x) c' κ₁ / S.th x₀ ∈ M.ringOn (U₀ : Set M.Z) := by
    rw [div_eq_mul_inv]
    exact mul_mem (hRU _ (FF_mem S (S.TT M x) c' κ₁)) (hO.th_unit x₀ hx₀.1)
  have heU' : (S.FF (S.TT M x) c' κ₁ / S.th x₀)⁻¹ ∈ M.ringOn (U₀ : Set M.Z) := by
    rw [inv_div, div_eq_mul_inv]
    exact mul_mem (hRU _ (S.th_mem x₀)) (hO.FF_unit (S.TT M x) c' κ₁ hiso hκ₁.1)
  have hpt : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y →
      spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y →
      0 < ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ₁ / S.th x₀)‖ ∧
      ‖M.val (gPt p ≫ y) ((S.FF (S.TT M x) c' κ₁ / S.th x₀) ^ S.N)‖ = ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ₁ / S.th x₀)‖ ^ S.N ∧
      (∀ α s, CongMod S.N α α₀ → PsiCoord D.toPre α s →
        ‖(ev s : PadicAlgCl p)‖ ≤ ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ₁ / S.th x₀)‖ ^ S.N) ∧
      ∃ mu s, CongMod S.N mu α₀ ∧ PsiCoord D.toPre mu s ∧
        ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ₁ / S.th x₀)‖ ^ S.N ≤ ‖(ev s : PadicAlgCl p)‖ := by
    intro p _ y ev hy hev
    have hrange : Set.range (gPt p ≫ y) = {(gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))} :=
      RatModel.range_eq_singleton _ _
    have hsp := RatModel.specializes_of_range_eq hrange
    have hz'U : (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)) ∈ (U₀ : Set M.Z) := hy.2 ⟨_, rfl⟩
    have hz'x := RatModel.gPt_specializes hy.1 (IsLocalRing.closedPoint (PadicAlgCl p))
    have heO := RatModel.ringOn_le_O hz'U heU
    have heO' := RatModel.ringOn_le_O hz'U heU'
    have hpos : 0 < ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ₁ / S.th x₀)‖ :=
      norm_pos_iff.2 ((RatModel.val_ne_zero_iff hrange ⟨_, heO⟩).2 ((RatModel.isUnit_O_iff _).2 ⟨he0, heO'⟩))
    have hpow : ‖M.val (gPt p ≫ y) ((S.FF (S.TT M x) c' κ₁ / S.th x₀) ^ S.N)‖ =
        ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ₁ / S.th x₀)‖ ^ S.N := by
      have := map_pow (RatModel.valHomOf (gPt p ≫ y) _ hsp) ⟨_, heO⟩ S.N
      rw [RatModel.valHomOf_apply, RatModel.valHomOf_apply] at this
      rw [← norm_pow, ← this]
      rfl
    have hle : ∀ κ, ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ / S.th x₀)‖ ≤
        ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ₁ / S.th x₀)‖ := by
      intro κ
      have hq : S.FF (S.TT M x) c' κ / S.FF (S.TT M x) c' κ₁ ∈ M.O x := hκ₁.2 κ
      have hq' := RatModel.O_le_of_specializes hz'x hq
      have eq : S.FF (S.TT M x) c' κ / S.th x₀ =
          (S.FF (S.TT M x) c' κ / S.FF (S.TT M x) c' κ₁) * (S.FF (S.TT M x) c' κ₁ / S.th x₀) := by
        have := hκ₁.1
        have := hx₀.1
        field_simp
      rw [eq, RatModel.val_mul hsp hq' heO, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (RatModel.norm_val_le_one hy.1 hq)
    obtain ⟨hlow, κ₂, hup⟩ := hc' p y ev hy hev x₀ hx₀
    refine ⟨hpos, hpow, fun α s hα hs => (hup α s hα hs).trans (pow_le_pow_left₀ (norm_nonneg _) (hle κ₂) _), ?_⟩
    exact hlow κ₁
  have hmem : (S.FF (S.TT M x) c' κ₁ / S.th x₀) ^ S.N ∈ M.O x := by
    refine _root_.GlobalTheory.Poinc.mem_O_of_norm_val_le_one o' Ω M hO.normal U₀ hO.ne x hx _ (pow_mem heU _) fun p _ y hy => ?_
    obtain ⟨ev, -, hev⟩ := hext p y hy
    obtain ⟨-, hpow, -, mu, s, -, -, h⟩ := hpt p y ev hy hev
    rw [hpow]
    exact h.trans ((mem_OO_iff _).1 (ev s).2)
  have hstalk : M.stalkHom x ((M.stalkEquiv x).symm ⟨_, hmem⟩) = (S.FF (S.TT M x) c' κ₁ / S.th x₀) ^ S.N := by
    rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
  have ha0 : (M.stalkEquiv x).symm ⟨_, hmem⟩ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hstalk
    exact pow_ne_zero _ he0 hstalk.symm
  have hva : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y →
      spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y →
      ((ev (j ((M.stalkEquiv x).symm ⟨_, hmem⟩)) : OO p) : PadicAlgCl p) =
        M.val (gPt p ≫ y) ((S.FF (S.TT M x) c' κ₁ / S.th x₀) ^ S.N) := by
    intro p _ y ev hy hev
    have hφ : spMap (ev.comp j) ≫ M.Z.fromSpecStalk x = y := by
      rw [← hev]
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have := GlobalTheory.CplDiv.val_stalkHom_eq o' Ω M x p y (ev.comp j) hy.1 hφ ((M.stalkEquiv x).symm ⟨_, hmem⟩)
    rw [hstalk] at this
    exact this.symm
  have hdvd : ∀ α s, CongMod S.N α α₀ → PsiCoord D.toPre α s → j ((M.stalkEquiv x).symm ⟨_, hmem⟩) ∣ s := by
    intro α s hα hs
    refine GlobalTheory.CplDiv.dvd_of_norm_le_at_classical o' Ω M hO.normal U₀ hO.ne x hx R j hj _ s ha0
      fun p _ y ev hy hev => ?_
    obtain ⟨-, hpow, hup, -⟩ := hpt p y ev hy hev
    rw [hva p y ev hy hev, hpow]
    exact hup α s hα hs
  obtain ⟨hpos₁, hpow₁, -, mu, smu, hmu, hsmu, hlow₁⟩ := hpt p₁ y₁ ev₁ hy₁ hev₁
  obtain ⟨t, ht⟩ := hdvd mu smu hmu hsmu
  have ht1 : 1 ≤ ‖((ev₁ t : OO p₁) : PadicAlgCl p₁)‖ := by
    have h := hlow₁
    rw [ht, map_mul, MulMemClass.coe_mul, norm_mul, hva p₁ y₁ ev₁ hy₁ hev₁, hpow₁] at h
    exact (le_mul_iff_one_le_right (pow_pos hpos₁ _)).1 h
  have htu : IsUnit t := by
    have hu : IsUnit (ev₁ t) := by
      by_contra hn
      exact absurd ((not_isUnit_OO_iff _).1 hn) (not_lt.2 ht1)
    exact isUnit_of_map_unit ev₁ t hu
  have hassoc : Associated (j ((M.stalkEquiv x).symm ⟨_, hmem⟩)) smu := ⟨htu.unit, by rw [ht, IsUnit.unit_spec]⟩
  refine ⟨mu, hmu, fun α hα r s hr hs => ?_, _, _, he0, ⟨S.TT M x, c', κ₁, x₀, hiso, rfl⟩, hstalk, fun r hr => ?_⟩
  · obtain ⟨u, hu⟩ := GlobalTheory.PsiCoordLocal.exists_unit_of_coord hsmu hr
    have : Associated (j ((M.stalkEquiv x).symm ⟨_, hmem⟩)) r := hassoc.trans ⟨u, by rw [hu, mul_comm]⟩
    exact this.symm.dvd.trans (hdvd α s hα hs)
  · obtain ⟨u, hu⟩ := GlobalTheory.PsiCoordLocal.exists_unit_of_coord hsmu hr
    exact hassoc.trans ⟨u, by rw [hu, mul_comm]⟩

end GlobalTheory.QUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordMultiplierOfSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mumfordMultiplier_of_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∀ N : ℕ, 1 ≤ N → GlobalTheory.MumMult.PosN D a h h' N → ∀ (σ₀ : LB.Sec (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1])) (x : D.toPre.P.A.left), D.toPre.P.A.hom x = (IsLocalRing.closedPoint R : PrimeSpectrum R) → GlobalTheory.MumMult.NonzeroAt D a N σ₀ x → ∃ m : ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), Γ((thickObj R (maximalIdeal R) e G).left, GlobalTheory.MumMult.multW U b e i i'), GlobalTheory.MumMult.MultAct U b N m ∧ GlobalTheory.MumMult.LeadPt U b m := by
  first | exact @GlobalTheory.MumMult.exists_mult_of_posN | exact GlobalTheory.MumMult.exists_mult_of_posN | (intros; apply GlobalTheory.MumMult.exists_mult_of_posN <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulEqOfTateModuleMapEqSmulStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nsmul_eq_of_tateModuleMap_eq_smul : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A B : AbVar K) (f : A ⟶ B) (φ : Tl l A →ₗ[ℤ_[l]] Tl l B), tmap l A B f = (l : ℤ_[l]) • φ → ∃ g : A ⟶ B, f = l • g := by
  first | (exact @GlobalTheory.AV.AbVar.exists_nsmul_eq_of_tmap_eq_smul) | (exact GlobalTheory.AV.AbVar.exists_nsmul_eq_of_tmap_eq_smul) | (intros; apply GlobalTheory.AV.AbVar.exists_nsmul_eq_of_tmap_eq_smul  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescalePsiW0
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiRescale

open GlobalTheory.PsiWZeroPull (prod_four)

section Geometry

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

abbrev FourGen (L : LB A.left) (f : A ⟶ A) : Type :=
  LB.Gen (LB.LinComb L (K := Fin 4) ![(padd A (𝟙 _) f).left, 𝟙 A.left, f.left, (toUnit A ≫ η[A]).left] ![1, -2, -1, 2])

theorem exists_normalised {L : LB A.left} (hL : L.IsLB) (f : A ⟶ A) [IsMonHom f] (u : FourGen L f) (hu : u.IsGen) :
    ∃ u' : FourGen L f, u'.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u' (eSec A)) (LB.oneGen L) := by
  obtain ⟨t, ht, hv⟩ := exists_gen hL
    (φ' := (![(padd A (𝟙 _) f).left, 𝟙 A.left, f.left, (toUnit A ≫ η[A]).left] : Fin 4 → _)) (ε' := ![1, -2, -1, 2])
    (fun V _ k => by
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := V) _ rfl
        (DVR.prod_neg _ _ (prod_four f (1 : A ⟶ A) k))) ?_
      rw [MonObj.one_comp, _root_.mul_one (1 : A ⟶ A)]
      refine mul_eq_left.2 (inv_eq_one.2 ?_)
      group)
    (LB.mulGen L _ _ _ _ u (LB.invGen L _ _ (LB.pullGen L _ _ u (1 : A ⟶ A).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _)))
  refine ⟨t, ht, corr_of_val hL fun y J hJ => ?_⟩
  have e : eSec A ≫ (1 : A ⟶ A).left = eSec A :=
    congrArg (fun q : 𝟙_ (Over S) ⟶ A => q.left) ((MonObj.comp_one (M := A) η[A]).trans (by simp [Hom.one_def]))
  rw [val_pull hJ, val_one, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, Category.assoc, e, mul_inv_cancel]

end Geometry

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]

open _root_.ReciprocityTheory.ChartRestriction.G.DVR (cP cPoint_add)

end GlobalTheory.PsiRescale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusTorsionPointOfLabelOrthogonalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torusTorsionPoint_of_label_orthogonal : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ, χ ^ (X₁.S.r * X₁.S.N) = 1 ∧ (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) := by
  first | exact @GlobalTheory.Poinc.Sep.TorPt.exists_torus_char | exact GlobalTheory.Poinc.Sep.TorPt.exists_torus_char | (intros; apply GlobalTheory.Poinc.Sep.TorPt.exists_torus_char <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfinitePairBounds
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FPair

theorem bil {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W →ₗ[K] K) (s s' : K) (u : V) (v : W) : f (s • u) (s' • v) = s * (s' * f u v) := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

private theorem full_grid_corner {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}
    {G : GridData L sc} {W : G.Weil} (S : GridChoice W Set.univ)
    (y : FinPt G (.grid D.R.m D.R.m)) :
    Submodule.IsFullLattice D.host.E (latAt S (.grid D.R.m D.R.m) y) := by
  have hsd := (G.isV (X := .grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩ fun j e => by
    have : D.R.m = 0 := (Node.grid.inj e).1
    have := D.R.two_le_m
    omega).sd
  have hΛ := GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hsd
  have hglob := Formalism.UG.P.csGlob_lattice (F := D.host.F) _
    (Module.Finite.iff_fg.2 hΛ.fg) hΛ.span_eq_top (finG (G.V (.grid D.R.m D.R.m)) y)
  let g := S.N.fr (.grid D.R.m D.R.m)
  let e : (Fin (G.V (.grid D.R.m D.R.m)).rank → D.host.E) ≃ₗ[D.host.E]
      (Fin (G.V (.grid D.R.m D.R.m)).rank → D.host.E) := LinearEquiv.ofLinearMap g.1.mulVecLin (g⁻¹).1.mulVecLin
    (by rw [← Matrix.mulVecLin_mul, Units.mul_inv, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, Units.inv_mul, Matrix.mulVecLin_one])
  haveI : Submodule.IsLattice D.host.E (latAt S (.grid D.R.m D.R.m) y) :=
    GlobalTheory.T.isLattice_vertexLattice_gridCorner S y
  refine ⟨?_⟩
  have hset : (latAt S (.grid D.R.m D.R.m) y : Set _) =
      e.symm '' (Formalism.UG.CS.globLat (finG (G.V (.grid D.R.m D.R.m)) y) (G.Λ (.grid D.R.m D.R.m)) : Set _) := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
    · rintro ⟨z, hz, rfl⟩
      change e (e.symm z) ∈ Formalism.UG.CS.globLat (finG (G.V (.grid D.R.m D.R.m)) y) (G.Λ (.grid D.R.m D.R.m))
      simpa using hz
  rw [hset, Submodule.span_image_linearEquiv, hglob.span_eq_top, Submodule.map_top, LinearEquiv.range]

theorem finPair : FinPairK := by
  obtain ⟨CF0, h6⟩ := GlobalTheory.T.exists_totalExponent_topWeight_bound
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨K0, h6'⟩ := h6 CF hCF
  refine ⟨max K0 0, fun ε C hC => ?_⟩
  obtain ⟨x₀, hx⟩ := h6' ε
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt _ => ?_⟩
  obtain ⟨hb1, Dn, hDn, hdiv, hlog⟩ := hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hIs hAt
  obtain ⟨h5mul, h5div, h5fin, h5sum⟩ := _root_.GlobalTheory.vw_lw_arith (K := D.what₂.LL)
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (le_trans (by norm_num) hS.size.2.2.2.1 : 1 ≤ D.R.m)
  have hsig : 0 ≤ sig ch.G := Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have hlb : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg hb1
  have hK : K0 ≤ C := (le_max_left _ _).trans hC
  have hC0 : 0 ≤ C := (le_max_right _ _).trans hC
  refine ⟨fun w => (Formalism.DivisionValues.vw w ((Dn : ℕ) : D.what₂.LL) : ℝ), ⟨fun w => ?_, ?_, fun s => ?_⟩, ?_⟩
  · show (0 : ℝ) ≤ (Formalism.DivisionValues.vw w ((Dn : ℕ) : D.what₂.LL) : ℝ)
    exact_mod_cast (h5div w Dn Dn hDn dvd_rfl).1
  · refine (h5fin Dn hDn).subset fun w hw => ?_
    intro h0
    exact hw (by simp [h0])
  · refine (h5sum Dn hDn s).trans (hlog.trans ?_)
    unfold bOne
    have e1 : 0 ≤ (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * large₂.sc.b * Real.log large₂.sc.b := by positivity
    have e2 : K0 * D.R.f * (bigN D : ℝ) ^ 2 * large₂.sc.b * Real.log large₂.sc.b ≤
        C * D.R.f * (bigN D : ℝ) ^ 2 * large₂.sc.b * Real.log large₂.sc.b := by
      have := mul_le_mul_of_nonneg_right hK e1
      linarith
    have e3 : C * D.R.f * (bigN D : ℝ) ^ 2 * large₂.sc.b * Real.log large₂.sc.b ≤
        C * D.R.f * D.R.m * (bigN D : ℝ) ^ 2 * (Real.log large₂.sc.b + sig ch.G) * large₂.sc.b := by
      have h1 : 0 ≤ C * D.R.f * (bigN D : ℝ) ^ 2 * large₂.sc.b := by positivity
      have h2 : Real.log large₂.sc.b ≤ D.R.m * (Real.log large₂.sc.b + sig ch.G) := by nlinarith
      have := mul_le_mul_of_nonneg_left h2 h1
      nlinarith
    exact e2.trans e3
  · intro w y a a' u v hu hv
    obtain ⟨u0, s, hu0, hs, hsa, hsu⟩ := hu
    obtain ⟨v0, s', hv0, hs', hsa', hsv⟩ := hv
    have hIS := fun τ => GlobalTheory.WtInterlace.weights_top_grid ch.G τ
    refine ⟨GlobalTheory.BrPairF.brPairF _ ch.G.sp.topDec.rank.symm _ u0 v0, ?_, ?_⟩
    · rw [← hu0, ← hv0]
      exact (GlobalTheory.T.branchingPairing_extendScalars D.what₂.embLL _ _ _ u0 v0).symm
    · have h4 := GlobalTheory.T.branchingPairing_integral_upToExponents (labLL D) ch.G.sp.topDec.rank.symm (wt ch.G (.top D.R.m)) (listedWt ch.G (.grid D.R.m D.R.m))
        (fun τ => (hIS τ).1) (fun τ => (hIS τ).2) _ _ (full_grid_corner ch.S.toGridChoice y) (GlobalTheory.T.mem_vertexLatticeOrthonormalCoords_topNode_iff ch.S.toGridChoice y) w
        (s • u0) (s' • v0) hsu hsv
      erw [bil] at h4
      by_cases hy : GlobalTheory.BrPairF.brPairF _ ch.G.sp.topDec.rank.symm _ u0 v0 = 0
      · exact Or.inl hy
      right
      rcases h4 with h0 | h4
      · exact absurd h0 (mul_ne_zero hs (mul_ne_zero hs' hy))
      rw [h5mul w _ _ hs (mul_ne_zero hs' hy), h5mul w _ _ hs' hy] at h4
      set p := Formalism.EigenvalueLevelCeiling.plc w
      set E := ∑ τ, Formalism.CohomologicalDescent.LA.exZ _ _ le_rfl (wt ch.G (.top D.R.m) τ).natW p
      have hp := (h5div w (p ^ E) Dn hDn (hdiv p (Formalism.EigenvalueLevelCeiling.plc_prime w))).2
      rw [Nat.cast_pow] at hp
      have h4' : (-(Formalism.DivisionValues.vw w ((p : D.what₂.LL) ^ E) : ℝ)) ≤
          (Formalism.DivisionValues.vw w s : ℝ) + ((Formalism.DivisionValues.vw w s' : ℝ) + (Formalism.DivisionValues.vw w (GlobalTheory.BrPairF.brPairF _ ch.G.sp.topDec.rank.symm _ u0 v0) : ℝ)) := by
        exact_mod_cast h4
      have hp' : (Formalism.DivisionValues.vw w ((p : D.what₂.LL) ^ E) : ℝ) ≤ (Formalism.DivisionValues.vw w ((Dn : ℕ) : D.what₂.LL) : ℝ) := by exact_mod_cast hp
      linarith

theorem infPair : InfPairK := by
  obtain ⟨CF0, h8⟩ := _root_.GlobalTheory.InfSize.main
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨K0, h8'⟩ := h8 CF hCF
  refine ⟨max K0 0, fun ε C hC => ?_⟩
  obtain ⟨x₀, hx⟩ := h8' ε
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt _ => ?_⟩
  obtain ⟨hb1, hlog⟩ := hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hIs hAt
  have hsig : 0 ≤ sig ch.G := Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have hlb : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg hb1
  have hK : K0 ≤ C := (le_max_left _ _).trans hC
  have hC0 : 0 ≤ C := (le_max_right _ _).trans hC
  have hIS := fun τ => GlobalTheory.WtInterlace.weights_top_grid ch.G τ
  set P := ∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd ch.G.sp.topDec.rank (wt ch.G (.top D.R.m) τ) (listedWt ch.G (.grid D.R.m D.R.m) τ) ^ 2 with hP
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun τ _ => sq_nonneg _
  have hPa : P ≤ Real.exp (aOne ch.G C large₂.sc.b) := by
    have h1 : Real.log P ≤ aOne ch.G C large₂.sc.b := by
      refine hlog.trans ?_
      unfold aOne
      have e1 : 0 ≤ (D.R.f : ℝ) * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by positivity
      have e2 : 0 ≤ C * D.R.m * (bigN D : ℝ) ^ 2 * sig ch.G := by positivity
      have := mul_le_mul_of_nonneg_right hK e1
      nlinarith
    rcases hP0.lt_or_eq with h | h
    · calc P = Real.exp (Real.log P) := (Real.exp_log h).symm
        _ ≤ _ := Real.exp_le_exp.2 h1
    · rw [← h]; exact (Real.exp_pos _).le
  intro σ B B' u v hu hv
  obtain ⟨u0, hu0, hB⟩ := hu
  obtain ⟨v0, hv0, hB'⟩ := hv
  refine ⟨GlobalTheory.BrPairF.brPairF _ ch.G.sp.topDec.rank.symm _ u0 v0, ?_, ?_⟩
  · rw [← hu0, ← hv0]
    exact (GlobalTheory.T.branchingPairing_extendScalars D.what₂.embLL _ _ _ u0 v0).symm
  · obtain ⟨hn1, hn2, h7⟩ := _root_.GlobalTheory.BrPairBound.inf_bound σ ch.G.sp.topDec.rank.symm (wt ch.G (.top D.R.m)) (listedWt ch.G (.grid D.R.m D.R.m))
      (fun τ => (hIS τ).1) (fun τ => (hIS τ).2) u0 v0
    refine h7.trans ?_
    have hB1 : (pairK (wt ch.G (.top D.R.m)) (fun _ => (1 : Matrix _ _ ℂ)) (GlobalTheory.CoefModel.mapVV σ _ u0)
        (GlobalTheory.CoefModel.mapVV σ _ u0)).re ≤ B := hB
    have hB2 : (pairK (fun τ => (listedWt ch.G (.grid D.R.m D.R.m) τ).dual) (fun _ => (1 : Matrix _ _ ℂ))
        (GlobalTheory.CoefModel.mapVV σ _ v0) (GlobalTheory.CoefModel.mapVV σ _ v0)).re ≤ B' := hB'
    have hPa' : (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd ch.G.sp.topDec.rank.symm.symm (wt ch.G (.top D.R.m) τ)
        (listedWt ch.G (.grid D.R.m D.R.m) τ) ^ 2) ≤ Real.exp (aOne ch.G C large₂.sc.b) := hPa
    have hP0' : 0 ≤ (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd ch.G.sp.topDec.rank.symm.symm (wt ch.G (.top D.R.m) τ)
        (listedWt ch.G (.grid D.R.m D.R.m) τ) ^ 2) := hP0
    have hBn : 0 ≤ B := hn1.trans hB1
    calc _ ≤ Real.exp (aOne ch.G C large₂.sc.b) * _ * _ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPa' hn1) hn2
      _ ≤ Real.exp (aOne ch.G C large₂.sc.b) * B * B' := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hB1 (Real.exp_pos _).le) hB2 hn2
          exact mul_nonneg (Real.exp_pos _).le hBn

end GlobalTheory.FPair

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasExtOfSetup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem Setup.hasExt (σ : Setup) : HasExt (awayMap σ.f) σ.A := by
  have hc : σ.Common := _root_.GlobalTheory.Desc.setup_common σ
  obtain ⟨E⟩ := _root_.GlobalTheory.Desc.nonempty_emb σ hc
  exact _root_.GlobalTheory.Desc.Emb.hasExt_of_locGrp σ E hc (_root_.GlobalTheory.Desc.UnionLocal.exists_locGrp_range_eq σ E hc)

theorem hasExt_of_setup : ∀ σ : Setup, HasExt (awayMap σ.f) σ.A := Setup.hasExt

end GlobalTheory.Desc
end

