use assert_cmd::{Command, cargo};
use std::sync::LazyLock;

#[track_caller]
fn cmd_output(cmd: &mut Command, should_error: bool) -> String {
    let output = cmd.output().expect("Failed to execute command");
    assert_ne!(
        should_error,
        output.status.success(),
        "CLI exited with unexpected error code: {}\nstderr:\n{}",
        output.status.code().unwrap(),
        std::str::from_utf8(&output.stderr).expect("Failed to convert stderr to string"),
    );
    String::from_utf8(output.stdout).expect("Failed to convert stdout to string")
}

static SETTINGS: LazyLock<insta::Settings> = LazyLock::new(|| {
    let mut settings = insta::Settings::clone_current();
    settings.set_filters([
        // negative integers, which are surrounded in parens
        (r"\(-\d+\)", "<integer>"),
        // positive integers, which are not surrounded in parens.
        // note that the redaction intentionally does not distinguish positive
        // from negative integers after the transform, because for some queries,
        // there may be valid counterexamples with both positive and negative
        // integers in a particular position
        //
        // We specifically look for integers following ": ", in order to ensure that
        // we do not redact text like "Found 2 request environment specific warnings"
        // -- we do want to make sure the number of warnings stays consistent, so we
        // want the 2 to remain. As of this writing, the only integers we need to redact
        // come immediately after ": ", not (say) inside sets.
        (r": \d+\b", ": <integer>"),
    ]);
    settings
});

/***************************************** Tests for Analysis *****************************************/
#[test]
fn test_analyze_policies_tabular_view_box_p1() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/view_box")
                .arg("analyze")
                .arg("policies")
                .arg("policies1.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_policies_tabular_view_box_p2() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/view_box")
                .arg("analyze")
                .arg("policies")
                .arg("policies2.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_policies_tabular_view_box_p3() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/view_box")
                .arg("analyze")
                .arg("policies")
                .arg("policies3.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_policies_tabular_view_box_p4() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/view_box")
                .arg("analyze")
                .arg("policies")
                .arg("policies4.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_policies_tabular_view_box_p5() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/view_box")
                .arg("analyze")
                .arg("policies")
                .arg("policies5.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_policies_tabular_online_docs() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/online_docs")
                .arg("analyze")
                .arg("policies")
                .arg("policies.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_view_box_trivial1() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/view_box")
                .arg("analyze")
                .arg("compare")
                .arg("permit_all.cedar")
                .arg("deny_all.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_view_box_trivial2() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/view_box")
                .arg("analyze")
                .arg("compare")
                .arg("deny_all.cedar")
                .arg("permit_all.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_view_box_trivial3() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/view_box")
                .arg("analyze")
                .arg("compare")
                .arg("empty.cedar")
                .arg("deny_all.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_view_box_trivial4() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/view_box")
                .arg("analyze")
                .arg("compare")
                .arg("permit_all.cedar")
                .arg("empty.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_view_box_basic_6_cmp_7() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/view_box")
                .arg("analyze")
                .arg("compare")
                .arg("policies6.cedar")
                .arg("policies7.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_view_box_basic_6_cmp_8() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/view_box")
                .arg("analyze")
                .arg("compare")
                .arg("policies6.cedar")
                .arg("policies8.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_view_box_basic_6_cmp_9() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/view_box")
                .arg("analyze")
                .arg("compare")
                .arg("policies6.cedar")
                .arg("policies9.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_view_box_basic_6_cmp_10() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/view_box")
                .arg("analyze")
                .arg("compare")
                .arg("policies6.cedar")
                .arg("policies10.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_arithmetic_1_cmp_2() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/arithmetic")
                .arg("analyze")
                .arg("compare")
                .arg("policies1.cedar")
                .arg("policies2.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_arithmetic_3_cmp_4() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/arithmetic")
                .arg("analyze")
                .arg("compare")
                .arg("policies3.cedar")
                .arg("policies4.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_arithmetic_3_cmp_5() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/arithmetic")
                .arg("analyze")
                .arg("compare")
                .arg("policies3.cedar")
                .arg("policies5.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_arithmetic_4_cmp_5() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/arithmetic")
                .arg("analyze")
                .arg("compare")
                .arg("policies4.cedar")
                .arg("policies5.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_arithmetic_7_cmp_9() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/arithmetic")
                .arg("analyze")
                .arg("compare")
                .arg("policies7.cedar")
                .arg("policies9.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_arithmetic_6_cmp_8() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/arithmetic")
                .arg("analyze")
                .arg("compare")
                .arg("policies6.cedar")
                .arg("policies8.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_arithmetic_7_cmp_10() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/arithmetic")
                .arg("analyze")
                .arg("compare")
                .arg("policies7.cedar")
                .arg("policies10.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_globs_a_star_cmp_a_star_star() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/globs")
                .arg("analyze")
                .arg("compare")
                .arg("a_star.cedar")
                .arg("a_star_star.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_globs_a_star_cmp_a_a_star() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/globs")
                .arg("analyze")
                .arg("compare")
                .arg("a_star.cedar")
                .arg("a_a_star.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_globs_a_star_cmp_a_star_non_a() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/globs")
                .arg("analyze")
                .arg("compare")
                .arg("a_star.cedar")
                .arg("a_star_non_a.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_globs_a_a_star_cmp_a_star_non_a() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/globs")
                .arg("analyze")
                .arg("compare")
                .arg("a_a_star.cedar")
                .arg("a_star_non_a.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_globs_a_star_star_a() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/globs")
                .arg("analyze")
                .arg("compare")
                .arg("a_star.cedar")
                .arg("star_a.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_globs_star_a_cmp_star_b() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/globs")
                .arg("analyze")
                .arg("compare")
                .arg("star_a.cedar")
                .arg("star_b.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_globs_a_cmp_star_other() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/globs")
                .arg("analyze")
                .arg("compare")
                .arg("a_star.cedar")
                .arg("other.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_sets1() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/sets")
                .arg("analyze")
                .arg("compare")
                .arg("src1.cedar")
                .arg("tgt1.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_sets2() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/sets")
                .arg("analyze")
                .arg("compare")
                .arg("src2.cedar")
                .arg("tgt2.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_sets3() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/sets")
                .arg("analyze")
                .arg("compare")
                .arg("src3.cedar")
                .arg("tgt3.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_sets4() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/sets")
                .arg("analyze")
                .arg("compare")
                .arg("src4.cedar")
                .arg("tgt4.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_sets5a() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/sets")
                .arg("analyze")
                .arg("compare")
                .arg("src5.cedar")
                .arg("tgt5a.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_sets5b() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/sets")
                .arg("analyze")
                .arg("compare")
                .arg("src5.cedar")
                .arg("tgt5b.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_sets5c() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/sets")
                .arg("analyze")
                .arg("compare")
                .arg("src5.cedar")
                .arg("tgt5c.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_sets6() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/sets")
                .arg("analyze")
                .arg("compare")
                .arg("src6.cedar")
                .arg("tgt6.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_sets7a() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/sets")
                .arg("analyze")
                .arg("compare")
                .arg("src7.cedar")
                .arg("tgt7a.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_sets7b() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/sets")
                .arg("analyze")
                .arg("compare")
                .arg("src7.cedar")
                .arg("tgt7b.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_misc1() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/misc")
                .arg("analyze")
                .arg("compare")
                .arg("src1.cedar")
                .arg("tgt1.cedar")
                .arg("policies1.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_policies_tabular_demo1() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/file_share_demo")
                .arg("analyze")
                .arg("policies")
                .arg("policies1.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_policies_tabular_demo2() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/file_share_demo")
                .arg("analyze")
                .arg("policies")
                .arg("policies2.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_policies_tabular_demo3() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/file_share_demo")
                .arg("analyze")
                .arg("policies")
                .arg("policies3.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_policies_tabular_demo4() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/file_share_demo")
                .arg("analyze")
                .arg("policies")
                .arg("policies4.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_demo_2_1() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/file_share_demo")
                .arg("analyze")
                .arg("compare")
                .arg("policies2.cedar")
                .arg("policies1.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_demo_3_2() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/file_share_demo")
                .arg("analyze")
                .arg("compare")
                .arg("policies3.cedar")
                .arg("policies2.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}

#[test]
fn test_analyze_compare_tabular_demo_4_3() {
    SETTINGS.bind(|| {
        insta::assert_snapshot!(cmd_output(
            &mut cargo::cargo_bin_cmd!()
                .current_dir("examples/analyze/file_share_demo")
                .arg("analyze")
                .arg("compare")
                .arg("policies4.cedar")
                .arg("policies3.cedar")
                .arg("policies.cedarschema"),
            false,
        ));
    });
}
