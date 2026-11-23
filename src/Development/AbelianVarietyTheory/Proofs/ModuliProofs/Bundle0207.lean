module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.WeilRos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0103
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ExponentialDifferential
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRescale
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.SymplecticBasisLevel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsDerivAt0NotIsDerivAlong
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsPreconnectedBlockUnits
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnLeftInverse
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUnifOfParts
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimTrivialOfMult
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasQuotOfIsIsogT
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory

open HeckePoint

theorem hasQuot_of_isIsogT : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o : Ob D l s) (t' : SAB H S) (ψ : o.t.G ⟶ t'.G) (K : Set o.t.G.left), 1 ≤ D.p + D.q → admitted l 𝔓 p → IsProper t'.G.hom → Out.RelAmple t'.G t'.PP.L → Out.KTriv t'.G t'.PP.L → IsIsogT o.t t' p ψ → KerSet ψ K → HeckeSet D o.t 𝔓 p i K → HasQuot o p K := by
  intro E _ _ _ H D l 𝔓 p i S _ s o t' ψ K _ ⟨h𝔓, hco, hp, hp𝔓, hpM⟩ hpr ham hkt hI hker hHk
  obtain ⟨hhom, hfin, het, hsur, hlin, hiso⟩ := hI
  have hG : Out.GlobalFnsSt := (show Out.Laws from GlobalTheory.firstFiveLaws.1).globalFns
  have hab := isAbelianScheme_of_proper o.t o.proper
  have hab' := isAbelianScheme_of_proper t' hpr
  have hW := fun (n : ℤ) (T : Over S) (x y : T ⟶ o.t.G) c c' =>
    weilIs_along_hom hG _ o.t.G t'.G ψ o.t.PP.L t'.PP.L (p ^ 2) n T x y c c' hab hab' o.t.PP.isLB t'.PP.isLB hhom hiso
  obtain ⟨p₀, hp₀⟩ := exists_inv_mod hp hpM
  have hMM : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have hAM : l.A ∣ l.M' := Nat.dvd_lcm_right _ _
  have etaM : ∀ a, o.eta (l.M • a) = 1 := fun a => o.eta_ker _ (by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul (natCast_M_mem l) Submodule.mem_top)
  let o' : Ob D l s :=
    { t := t', proper := hpr, ample := ham, ktriv := hkt
      eta := fun a => o.eta (p₀ • a) ≫ ψ
      eta_add := fun a c => by rw [smul_add, o.eta_add, MonObj.mul_comp]
      eta_ker := fun a ha => by rw [o.eta_ker _ (nsmul_mem ha _), MonObj.one_comp]
      etaA := fun a => o.etaA (p₀ • a) ≫ ψ
      etaA_add := fun a c => by rw [smul_add, o.etaA_add, MonObj.mul_comp]
      etaA_ker := fun a => by rw [smul_comm, o.etaA_ker, MonObj.one_comp]
      geom := by
        intro k _ _ x β hx
        obtain ⟨hdet, I, hζ, hA, hM⟩ := o.geom k x β hx
        refine ⟨fun τ => ?_, ?_⟩
        · simp only [← LieEtale.lieMult_iff_of_etale _ _ _ _ ψ o.t.act t'.act hhom het hlin k x τ]
          exact hdet τ
        obtain ⟨C, hC, -, c₂, c₃, c₄, c₅, -⟩ := hHk k x
        have mem : ∀ z : Over.mk x ⟶ o.t.G, z ≫ ψ = 1 ↔ z ∈ C := fun z => (hker k x z).trans (hC z).symm
        let ψx : (Over.mk x ⟶ o.t.G) →* (Over.mk x ⟶ t'.G) :=
          MonoidHom.mk' (fun z => z ≫ ψ) fun a c => MonObj.mul_comp a c ψ
        have uniq : ∀ (n : ℤ) (z w : Over.mk x ⟶ o.t.G) (c c' : kˣ),
            Out.WeilIs o.t.G o.t.PP.L n z w (unitOn c) → Out.WeilIs o.t.G o.t.PP.L n z w (unitOn c') → c = c' :=
          fun n z w c c' h h' => (unitOn_bijective k).1 (CommutatorPairing.weilIs_unique hG hab o.t.PP.isLB h h')
        obtain ⟨I', hζ', hev⟩ := exists_tateIso_heckeQuotient SimAlg.sim_group E H D 𝔓 p k _ _ _
          (fun a g => g ≫ t'.act.act a) _
          (fun n g g' c => Out.WeilIs t'.G t'.PP.L n g g' (unitOn c)) I ψx h𝔓 hco hp hp𝔓
          (fun y => exists_lift_pt ψ x y)
          (fun a z => by
            show (z ≫ _) ≫ ψ = (z ≫ ψ) ≫ _
            rw [Category.assoc, hlin, Category.assoc])
          (fun J hJ z _ hz' => (mem z).2 (c₂ J hJ hz'))
          (fun z hz => ⟨by
            rw [← comp_act_natCast o.t.act]
            refine c₃ ((mem z).1 hz) _ ?_
            rw [Nat.cast_pow, pow_two]
            refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
            have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hp𝔓
            rwa [map_natCast] at this, c₃ ((mem z).1 hz)⟩)
          (fun z w hz hw => by
            have h := c₄ z ((mem z).1 hz) w ((mem w).1 hw)
            rw [← Nat.cast_pow] at h
            exact (congrArg (Out.WeilIs o.t.G o.t.PP.L ((p ^ 2 : ℕ) : ℤ) z w) unitOn_one).mpr h)
          (by rw [← c₅, show ψx.ker = C from Subgroup.ext mem])
          (fun n z w c c' _ _ _ h h' => uniq n z w c c' h h')
          (fun n z w c hn hz hw h => by
            have hlift : ∀ (q : Over.mk x ⟶ t'.G), q ^ n = 1 →
                ∀ a : (Over.mk x).left, ∃ V : (Over.mk x).left.Opens, a ∈ V ∧
                  ∃ θ : Out.ThetaGrp t'.G t'.PP.L n (Out.overRes V), θ.pt = Out.overResι V ≫ q := by
              intro q hq a
              obtain ⟨V, hV, v, hv⟩ := exists_local_gen t'.PP.isLB (K := Fin 2)
                ![(1 : Over.mk x ⟶ t'.G).left, q.left] ![(n : ℤ), -(n : ℤ)] a
              refine ⟨V, hV, ?_⟩
              apply exists_theta t'.cub (by rw [← MonObj.comp_pow, hq, MonObj.comp_one]) v hv
              intro U _ f
              rw [Fin.prod_univ_two, ← MonObj.comp_one (Out.overResι V)]
              rfl
            obtain ⟨c', hc'⟩ := CommutatorPairing.exists_weilIs hG hab' t'.PP.isLB (hlift _ hz) (hlift _ hw)
            obtain ⟨c', rfl⟩ := (unitOn_bijective k).2 c'
            have h₂ := (hW n _ z w 1 _ hc').1
            rw [← Nat.cast_mul] at h₂
            rw [uniq _ z w c c' h h₂]
            exact hc')
        refine ⟨I', by rw [hζ']; exact hζ, fun a => ?_, fun a ha => ?_⟩
        · rw [hev l.A p₀ l.A_pos (hp₀.of_dvd hAM), ← hA, ← Category.assoc]; rfl
        · rw [hev l.M p₀ (by have := l.three_le; omega) (hp₀.of_dvd hMM), ← hM _ (nsmul_mem ha _),
            ← Category.assoc]; rfl }
  refine ⟨o', ψ, ⟨⟨hhom, hfin, het, hsur, hlin, hiso⟩, fun p' hp' a => ?_⟩, hker⟩
  have e := modEq_of_inv hp' hp₀
  exact ⟨congrArg (· ≫ ψ) (eq_of_modEq o.eta o.eta_add etaM (e.of_dvd hMM) a),
    congrArg (· ≫ ψ) (eq_of_modEq o.etaA o.etaA_add o.etaA_ker (e.of_dvd hAM) a)⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KeyFormulaIffClauses
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyFormulaCompare

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

def Same (u : HolUnif A L g) (F : Unif A L g) : Prop :=
  F.exp = u.ex ∧ ∀ i z h, F.fr i z h = u.fr i z

namespace Same

variable {u : HolUnif A L g} {F : Unif A L g} (h : Same u F)
include h

end Same

end Unif

section Analytic

end Analytic

section Principal

theorem tangent_bijective (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) :
    (∀ v, Geo.Tor.IsTangent v → ∃! w, u.IsDiff w v) ∧ ∀ w, ∃! v, Geo.Tor.IsTangent v ∧ u.IsDiff w v := by
  obtain ⟨u₀, H₀, χ₀, E₀, -, -, hv, hw, -⟩ := thetaUnifAV_closed x.P x.rig x.rig_gen
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo x.P.A x.P.isAb x.P.L x.P.g x.P.g u₀ hv hw u.ex
    u.ex_add (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  let e : (Fin x.P.g → ℂ) ≃ₗ[ℂ] (Fin x.P.g → ℂ) := LinearEquiv.ofInjectiveEndo F (UnifCompare.injective u u₀ F hF)
  have hd : ∀ w v, u.IsDiff w v ↔ u₀.IsDiff (e w) v :=
    UnifCompare.isDiff_iff u u₀ e.toContinuousLinearEquiv hF
  refine ⟨fun v hv' => ?_, fun w => ?_⟩
  · obtain ⟨w, h1, h2⟩ := hv v hv'
    refine ⟨e.symm w, (hd _ _).2 (by rwa [e.apply_symm_apply]), fun y hy => ?_⟩
    rw [← h2 _ ((hd _ _).1 hy), e.symm_apply_apply]
  · simp only [hd]
    exact hw (e w)

theorem det_ne_zero (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ)
    (hW : ∀ i, u.IsDiff (W i) (x.v i)) : W.det ≠ 0 := by
  obtain ⟨h₁, h₂⟩ := tangent_bijective x u
  refine ((Matrix.isUnit_iff_isUnit_det W).1 (Matrix.vecMul_surjective_iff_isUnit.1 fun w => ?_)).ne_zero
  obtain ⟨v, hv, hd⟩ := (h₂ w).exists
  obtain ⟨c, hc⟩ := (x.basis.2 v hv).exists
  exact ⟨c, (Matrix.vecMul_eq_sum c W).trans ((h₁ v hv).unique
    (UnifDifferential.isDiff_of_isLieComb _ _ _ _ u W x.v c v x.basis.1 hW hc) hd)⟩

end Principal

section Clauses

abbrev RuleIn : Type 1 := ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ

variable (κ : RuleIn)

end Clauses

end GlobalTheory.KeyFormulaCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyFamilyUnifIffUnifAt
section
noncomputable section

namespace GlobalTheory.UnifCompare

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTypeFn IsThetaFrame
open GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation hiding IsTypeFn IsThetaFrame
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticBasisLevel GlobalTheory.PeriodCompare
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Lattice

theorem isPeriod_move {D' : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P₀ P₁ P : D'.La →+ (Fin g → ℂ)}
    (h₀ : IsPeriod D' ty P₀) (h₁ : IsPeriod D' ty P₁) (hP : IsPeriod D' ty P) (gam : D'.La ≃ₗ[𝓞 E] D'.La)
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hgam : ∀ a b, D'.EF (gam a) (gam b) = D'.EF a b)
    (hh : ∀ a, P₁ (gam a) = h (P₀ a)) :
    IsPeriod D' ty (h.toLinearMap.toAddMonoidHom.comp (P.comp gam.symm.toLinearMap.toAddMonoidHom)) := by
  have tr : ∀ {Q : D'.La →+ (Fin g → ℂ)}, IsPeriod D' ty Q →
      IsPeriod D' ty (Q.comp gam.symm.toLinearMap.toAddMonoidHom) := by
    rintro Q ⟨h1, h2, h3, h4, Hm, h5, h6, h7⟩
    have hr : (Q.comp gam.symm.toLinearMap.toAddMonoidHom).range = Q.range :=
      SetLike.ext' (gam.symm.surjective.range_comp Q)
    refine ⟨fun a x i => ?_, h2.comp gam.symm.injective, by rw [hr]; exact h3, ?_, Hm, h5, h6, fun x y => ?_⟩
    · simpa using h1 a (gam.symm x) i
    · rw [← h4, ← AddMonoidHom.coe_range, hr, AddMonoidHom.coe_range]
    · change (hermForm Hm (Q (gam.symm x)) (Q (gam.symm y))).im = _
      rw [h7, ← hgam, gam.apply_symm_apply, gam.apply_symm_apply]
  let A := LinearMap.toMatrix' h.toLinearMap
  have hA : A.mulVecLin = h.toLinearMap := by
    rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
  have hdet : A.det ≠ 0 := by
    rw [LinearMap.det_toMatrix']
    exact h.isUnit_det'.ne_zero
  rw [← hA]
  refine PeriodConn.isPeriod_mulVec (tr hP) hdet (PeriodConn.entry_eq_zero (tr h₀) h₁ fun x => ?_)
  rw [← Matrix.mulVecLin_apply, hA]
  exact (congrArg P₁ (gam.apply_symm_apply x)).symm.trans (hh _)

variable {g : ℕ}

variable {D' : Datum H} {ty : Fin g → (E →+* ℂ)}

end Lattice

section Deriv

variable {X S : Scheme.{0}} {g : ℕ}

theorem isDerivAt0_smul {F : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ X}
    (hv : IsDerivAt0 F w v) (c : ℂ) : IsDerivAt0 F (c • w) (spMap (epsScale c) ≫ v) := by
  have h0 : spMap TangentOrigin.fstC ≫ spMap (epsScale c) ≫ v = spMap TangentOrigin.fstC ≫ v := by
    rw [← Category.assoc, TanMod.spMap_comp']
    congr 2
    exact RingHom.ext fun x => by simp [epsScale]
  refine ⟨h0.trans hv.1, fun U h f => ?_⟩
  have h' : ⊤ ≤ v ⁻¹ᵁ U := by
    rw [TangentOrigin.top_le_preimage_iff] at h ⊢
    exact h0 ▸ h
  refine (congrArg TrivSqZeroExt.snd (TangentOrigin.evalPt_spMap_comp (epsScale c) v U h' h f)).trans ?_
  rw [map_smul, ← hv.2 U h' f]
  exact TrivSqZeroExt.snd_map _ _

theorem isDerivAt0_mul {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {F : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)}
    (h0 : F 0 = (1 : Over.mk y ⟶ G).left) {w w' : Fin g → ℂ} {v v' : epsPt y ⟶ G}
    (hv : IsDerivAt0 F w v.left) (hv' : IsDerivAt0 F w' v'.left) : IsDerivAt0 F (w + w') (v * v').left := by
  have t := TanMod.smT_zero_of y v (hv.1.trans h0)
  have t' := TanMod.smT_zero_of y v' (hv'.1.trans h0)
  have t'' : spMap TangentOrigin.fstC ≫ (v * v').left = F 0 :=
    (TanMod.unit_of_smT_zero y (v * v') (by rw [TanMod.smT_mul, t, t', _root_.mul_one])).trans h0.symm
  refine ⟨t'', fun U h f => ?_⟩
  have hF : ⊤ ≤ F 0 ⁻¹ᵁ U := t'' ▸ (TangentOrigin.top_le_preimage_iff _ U).1 h
  have h1 := (TangentOrigin.top_le_preimage_iff v.left U).2 (hv.1.symm ▸ hF)
  have h2 := (TangentOrigin.top_le_preimage_iff v'.left U).2 (hv'.1.symm ▸ hF)
  rw [map_add (f := _), ← hv.2 U h1 f, ← hv'.2 U h2 f]
  exact TanDeriv.snd_evAt_mul v v' t t' U h1 h2 h f

end Deriv

section Piece

variable {D : Datum H} {l : Level H} (Xo : Moduli D l) {g : ℕ} (ty : Fin g → (E →+* ℂ))
  (D' : Datum H) (u : (D'.La →+ (Fin g → ℂ)) → (Sp ℂ ⟶ Xo.X))
  (ex : ∀ P : D'.La →+ (Fin g → ℂ), (Fin g → ℂ) → (Over.mk (u P) ⟶ univG Xo))

variable {Xo ty D' u ex}

end Piece

section Main

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

end Main

end GlobalTheory.UnifCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmplePrincipalDescendedBundleNoetherian
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.DescentFamily

open GlobalTheory.CechPic

theorem card_ker_pullback {S S' : Scheme.{0}} (t : S' ⟶ S) {A B : Over S} [GrpObj A] [GrpObj B] (ψ : A ⟶ B) :
    Nat.card {x : 𝟙_ (Over S') ⟶ (Over.pullback t).obj A // x ≫ (Over.pullback t).map ψ = 1} =
      Nat.card {x : Over.mk ((𝟙_ (Over S')).hom ≫ t) ⟶ A // x ≫ ψ = 1} := by
  have hA := isGrpPullback_pullback A t
  have hB := isGrpPullback_pullback B t
  have inj : ∀ {G : Over S} [GrpObj G] (h : IsGrpPullback ((Over.pullback t).obj G) G t (pullback.fst G.hom t)),
      Function.Injective (pushHom h (𝟙_ (Over S'))) := fun h x y e =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun z => z.left) e) (by rw [Over.w, Over.w]))
  have surj : Function.Surjective (pushHom hA (𝟙_ (Over S'))) := fun x =>
    ⟨Over.homMk (hA.1.lift x.left (𝟙_ (Over S')).hom (Over.w x)) (hA.1.lift_snd _ _ _),
      Over.OverMorphism.ext (hA.1.lift_fst _ _ _)⟩
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective _ ⟨inj hA, surj⟩) fun x => ?_)
  have e : pushHom hB (𝟙_ (Over S')) (x ≫ (Over.pullback t).map ψ) = pushHom hA (𝟙_ (Over S')) x ≫ ψ := by
    refine Over.OverMorphism.ext ?_
    show (x.left ≫ ((Over.pullback t).map ψ).left) ≫ pullback.fst B.hom t = (x.left ≫ pullback.fst A.hom t) ≫ ψ.left
    rw [Category.assoc, Category.assoc]
    exact congrArg (x.left ≫ ·) (pullback.lift_fst _ _ _)
  exact (map_eq_one_iff _ (inj hB)).symm.trans (Eq.congr_left e)

theorem kTriv_fibre {S : Scheme.{0}} (P : Out.PolAV S) {n : ℕ} (B : Over S) [GrpObj B] (ψ : P.A ⟶ B) (M : LB B.left)
    (hn : 0 < n) (hB : IsAbelianScheme B) (hM : M.IsLB) [IsMonHom ψ] [IsFinite ψ.left] [Etale ψ.left]
    [Surjective ψ.left] (hiso : LBIso (lbPow P.L n) (M.pull ψ.left)) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (t : Sp k ⟶ S) (hc : Nat.card {x : Over.mk (𝟙 _ ≫ t) ⟶ P.A // x ≫ ψ = 1} = n ^ P.g) :
    Out.KTriv ((Over.pullback t).obj B) (M.pull (pullback.fst B.hom t)) := by
  have hw : ((Over.pullback t).map ψ).left ≫ pullback.fst B.hom t = pullback.fst P.A.hom t ≫ ψ.left :=
    pullback.lift_fst _ _ _
  have hp : IsPullback (pullback.fst P.A.hom t) ((Over.pullback t).map ψ).left ψ.left (pullback.fst B.hom t) := by
    refine IsPullback.of_bot ?_ hw.symm (IsPullback.of_hasPullback B.hom t)
    have e : ((Over.pullback t).map ψ).left ≫ pullback.snd B.hom t = pullback.snd P.A.hom t :=
      Over.w ((Over.pullback t).map ψ)
    rw [e, Over.w ψ]
    exact IsPullback.of_hasPullback _ _
  have hL' := pull_isLB P.isLB (pullback.fst P.A.hom t)
  have hM' := pull_isLB hM (pullback.fst B.hom t)
  have h₁ : (lbPow (P.L.pull (pullback.fst P.A.hom t)) n).IsLB := LB.isLB_linComb hL' _ _
  have h₂ := pull_isLB hM' ((Over.pullback t).map ψ).left
  have h₀ := (cls_eq_iff (LB.isLB_linComb P.isLB _ _) (pull_isLB hM _)).2 hiso
  rw [cls_lbPow P.isLB, cls_pull hM] at h₀
  have he : cls _ h₁ = cls _ h₂ := by
    rw [cls_lbPow hL', cls_pull hM', cls_pull P.isLB, cls_pull hM, ← pull_comp, hw, pull_comp, ← h₀, map_nsmul]
  have hmon : IsMonHom ((Over.pullback t).map ψ) := inferInstance
  have H := pol_pull _ _ P.A ((Over.pullback t).obj P.A) t (pullback.fst P.A.hom t)
    P.L _ P.isLB hL' P.isAb (isGrpPullback_pullback P.A t) (PolBaseChange.lbIso_refl hL')
  let Q : Out.PolAV (Sp k) :=
    { A := (Over.pullback t).obj P.A, isAb := H.1, g := P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (isGrpPullback_pullback P.A t).1 P.smoothDim
      L := P.L.pull (pullback.fst P.A.hom t), isLB := hL'
      rigid := PolBaseChange.rigidified_pull (isGrpPullback_pullback P.A t) P.rigid
      sym := PolBaseChange.sym_pull (isGrpPullback_pullback P.A t) P.sym
      ample := H.2.1 P.ample, ktriv := H.2.2 P.ktriv }
  refine kTriv_of_descent firstFiveLaws.1 k Q n _ ((Over.pullback t).map ψ) _ hn
    (PolPull.isAbelianScheme_of_isGrpPullback hB (isGrpPullback_pullback B t)) hM' hmon
    (MorphismProperty.of_isPullback (P := @IsFinite) hp inferInstance)
    (MorphismProperty.of_isPullback (P := @Etale) hp inferInstance)
    (MorphismProperty.of_isPullback (P := @Surjective) hp inferInstance)
    ((card_ker_pullback t ψ).trans hc) ?_
  refine (cls_eq_iff (LB.isLB_linComb h₁ _ _) (LB.isLB_linComb h₂ _ _)).1 ?_
  refine (cls_cube_two (G := (Over.pullback t).obj P.A) h₁ _ _ _).trans
    (Eq.trans ?_ (cls_cube_two (G := (Over.pullback t).obj P.A) h₂ _ _ _).symm)
  exact congrArg (fun c => lam (G := (Over.pullback t).obj P.A) c _ _) he

end GlobalTheory.DescentFamily

namespace GlobalTheory

open GlobalTheory.CechPic

theorem relAmple_kTriv_of_descent_family : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)) (n : ℕ) (B : Over (Sp R)) [GrpObj B] (ψ : P.A ⟶ B) (M : LB B.left), (∀ m : ℕ, 0 < m → IsUnit (m : R)) → 0 < n → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R), Nat.card {x : Over.mk t ⟶ P.A // x ≫ ψ = 1} = n ^ P.g) → LBIso (lbPow P.L n) (M.pull ψ.left) → Out.RelAmple B M ∧ Out.KTriv B M := by
  intro R _ _ P n B _ ψ M hu hn hB hM hψ hf he hs hc hiso
  have hA := P.isAb
  have hn' : (lbPow P.L n).IsLB := LB.isLB_linComb P.isLB _ _
  have hid : IsFinite (𝟙 P.A : P.A ⟶ P.A).left := by rw [Over.id_left]; infer_instance
  have a₁ : Out.RelAmple P.A (lbPow P.L n) :=
    (relAmple_finite_pow_iso _ P.A P.A (𝟙 _) P.L n hn hA hA P.isLB hid).2.1.2 P.ample
  have a₂ : Out.RelAmple P.A (M.pull ψ.left) :=
    (relAmple_finite_pow_iso _ P.A P.A (𝟙 _) _ 1 one_pos hA hA hn' hid).2.2.2 _ (pull_isLB hM _) hiso a₁
  have a₃ : Out.RelAmple B M :=
    (relAmple_finite_pow_iso _ P.A B ψ M 1 one_pos hA hB hM hf).2.2.1 inferInstance hs a₂
  refine ⟨a₃, ?_⟩
  have loc : ∀ q : PrimeSpectrum R, ∃ f : R, f ∉ q.asIdeal ∧
      Out.KTriv ((Over.pullback (spMap (algebraMap R (Localization.Away f)))).obj B)
        (M.pull (pullback.fst B.hom (spMap (algebraMap R (Localization.Away f))))) := by
    intro q
    let k := AlgebraicClosure q.asIdeal.ResidueField
    let x : R →+* k := (algebraMap q.asIdeal.ResidueField k).comp (algebraMap R q.asIdeal.ResidueField)
    have : CharZero k := charZero_of_inj_zero fun m hm => by
      by_contra h
      have := (hu m (Nat.pos_of_ne_zero h)).map x
      rw [map_natCast, hm] at this
      exact not_isUnit_zero this
    obtain ⟨f, hf, H⟩ := kTriv_away_of_kTriv_fibre firstFiveLaws.1.globalFns R B M k x hB hM a₃
      (DescentFamily.kTriv_fibre P B ψ M hn hB hM hiso k (spMap x) (hc k _))
    refine ⟨f, fun h => hf ?_, H⟩
    show algebraMap q.asIdeal.ResidueField k (algebraMap R q.asIdeal.ResidueField f) = 0
    rw [Ideal.algebraMap_residueField_eq_zero.2 h, map_zero]
  choose f hf H using loc
  let j : ∀ q, Sp (Localization.Away (f q)) ⟶ Sp R := fun q => spMap (algebraMap R (Localization.Away (f q)))
  have hj : ∀ q, IsOpenImmersion (j q) := fun q => IsOpenImmersion.of_isLocalization (f q)
  let G := fun q => (Over.pullback (j q).isoOpensRange.inv).obj ((Over.pullback (j q)).obj B)
  have gp : ∀ q, IsGrpPullback (G q) ((Over.pullback (j q)).obj B) (j q).isoOpensRange.inv (pullback.fst _ _) :=
    fun q => isGrpPullback_pullback _ _
  have hM₁ := fun q => pull_isLB hM (pullback.fst B.hom (j q))
  have hB₁ := fun q => PolPull.isAbelianScheme_of_isGrpPullback hB (isGrpPullback_pullback B (j q))
  have key := fun q => pol_pull _ _ _ (G q) _ _ _ _ (hM₁ q) (pull_isLB (hM₁ q) _) (hB₁ q) (gp q)
    ((cls_eq_iff (pull_isLB (hM₁ q) _) (pull_isLB (hM₁ q) _)).1 rfl)
  refine CoverGlue.kTriv_of_cover (Sp R) (PrimeSpectrum R) (fun q => (j q).opensRange) B G
    (fun q => pullback.fst _ (j q).isoOpensRange.inv ≫ pullback.fst B.hom (j q)) ?_
    (fun q => ((gp q).comp (isGrpPullback_pullback B (j q))).congr (Scheme.Hom.isoOpensRange_inv_comp _) rfl)
    M _ hM (fun q => pull_isLB (hM₁ q) _) (fun q => ?_) hB (fun q => (key q).1) (fun q => (key q).2.2 (H q))
  · refine top_le_iff.1 fun q _ => TopologicalSpace.Opens.mem_iSup.2 ⟨q, ?_⟩
    have : q ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away (f q)))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (f q)) (f q)]
      exact hf q
    exact this
  · rw [← cls_eq_iff (pull_isLB (hM₁ q) _) (pull_isLB hM _), cls_pull (hM₁ q), cls_pull hM, cls_pull hM, pull_comp]

end GlobalTheory
end
end

