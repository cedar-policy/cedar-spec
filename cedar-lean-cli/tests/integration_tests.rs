use std::process::{Command, Output};
use std::path::{Path, PathBuf};

fn check_output<P: AsRef<Path>>(
    output : Output,
    expected_output_file : P,
    should_error: bool,
) {
    let cli_output = std::str::from_utf8(&output.stdout)
        .expect("Failed to convert output to string").to_string();
    let expected_output = std::fs::read_to_string(expected_output_file.as_ref())
        .expect("Failed to read expected output file");

    assert!(should_error != output.status.success(), "CLI exited with unexpected error code: {}", output.status.code().unwrap());
    assert_eq!(cli_output.trim(), expected_output.trim(), "CLI output does not match expected output")
}

/***************************************** Tests for Analysis *****************************************/
#[test]
fn test_analyze_policies_tabular_view_box_p1() {
    let base_path = PathBuf::from("examples/analyze/view_box");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("policies")
        .arg(base_path.join("policies1.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

        check_output(output, base_path.join("outputs/tabular/policies1.out"), false)
}

#[test]
fn test_analyze_policies_tabular_view_box_p2() {
    let base_path = PathBuf::from("examples/analyze/view_box");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("policies")
        .arg(base_path.join("policies2.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/policies2.out"), false)
}

#[test]
fn test_analyze_policies_tabular_view_box_p3() {
    let base_path = PathBuf::from("examples/analyze/view_box");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("policies")
        .arg(base_path.join("policies3.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/policies3.out"), false)
}

#[test]
fn test_analyze_policies_tabular_view_box_p4() {
    let base_path = PathBuf::from("examples/analyze/view_box");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("policies")
        .arg(base_path.join("policies4.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/policies4.out"), false)
}

#[test]
fn test_analyze_policies_tabular_view_box_p5() {
    let base_path = PathBuf::from("examples/analyze/view_box");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("policies")
        .arg(base_path.join("policies5.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/policies5.out"), false)
}

#[test]
fn test_analyze_policies_tabular_online_docs() {
    let base_path = PathBuf::from("examples/analyze/online_docs");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("policies")
        .arg(base_path.join("policies.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/policies.out"), false)
}

#[test]
fn test_analyze_compare_tabular_view_box_trivial1() {
    let base_path = PathBuf::from("examples/analyze/view_box");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("permit_all.cedar"))
        .arg(base_path.join("deny_all.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/compare_trivial1.out"), false)
}

#[test]
fn test_analyze_compare_tabular_view_box_trivial2() {
    let base_path = PathBuf::from("examples/analyze/view_box");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("deny_all.cedar"))
        .arg(base_path.join("permit_all.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/compare_trivial2.out"), false)
}

#[test]
fn test_analyze_compare_tabular_view_box_trivial3() {
    let base_path = PathBuf::from("examples/analyze/view_box");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("empty.cedar"))
        .arg(base_path.join("deny_all.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/compare_trivial3.out"), false)
}

#[test]
fn test_analyze_compare_tabular_view_box_trivial4() {
    let base_path = PathBuf::from("examples/analyze/view_box");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("permit_all.cedar"))
        .arg(base_path.join("empty.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/compare_trivial4.out"), false)
}

#[test]
fn test_analyze_compare_tabular_view_box_basic_6_cmp_7() {
    let base_path = PathBuf::from("examples/analyze/view_box");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("policies6.cedar"))
        .arg(base_path.join("policies7.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/compare_basic_6_7.out"), false)
}

#[test]
fn test_analyze_compare_tabular_view_box_basic_6_cmp_8() {
    let base_path = PathBuf::from("examples/analyze/view_box");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("policies6.cedar"))
        .arg(base_path.join("policies8.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/compare_basic_6_8.out"), false)
}

#[test]
fn test_analyze_compare_tabular_view_box_basic_6_cmp_9() {
    let base_path = PathBuf::from("examples/analyze/view_box");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("policies6.cedar"))
        .arg(base_path.join("policies9.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/compare_basic_6_9.out"), false)
}

#[test]
fn test_analyze_compare_tabular_view_box_basic_6_cmp_10() {
    let base_path = PathBuf::from("examples/analyze/view_box");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("policies6.cedar"))
        .arg(base_path.join("policies10.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/compare_basic_6_10.out"), false)
}

#[test]
fn test_analyze_compare_tabular_arithmetic_1_cmp_2() {
    let base_path = PathBuf::from("examples/analyze/arithmetic");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("policies1.cedar"))
        .arg(base_path.join("policies2.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/compare_1_2.out"), false)
}

#[test]
fn test_analyze_compare_tabular_arithmetic_3_cmp_4() {
    let base_path = PathBuf::from("examples/analyze/arithmetic");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("policies3.cedar"))
        .arg(base_path.join("policies4.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/compare_3_4.out"), false)
}

#[test]
fn test_analyze_compare_tabular_arithmetic_3_cmp_5() {
    let base_path = PathBuf::from("examples/analyze/arithmetic");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("policies3.cedar"))
        .arg(base_path.join("policies5.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/compare_3_5.out"), false)
}

#[test]
fn test_analyze_compare_tabular_arithmetic_4_cmp_5() {
    let base_path = PathBuf::from("examples/analyze/arithmetic");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("policies4.cedar"))
        .arg(base_path.join("policies5.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/compare_4_5.out"), false)
}

#[test]
fn test_analyze_compare_tabular_arithmetic_7_cmp_9() {
    let base_path = PathBuf::from("examples/analyze/arithmetic");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("policies7.cedar"))
        .arg(base_path.join("policies9.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/compare_7_9.out"), false)
}

#[test]
fn test_analyze_compare_tabular_arithmetic_6_cmp_8() {
    let base_path = PathBuf::from("examples/analyze/arithmetic");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("policies6.cedar"))
        .arg(base_path.join("policies8.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/compare_6_8.out"), false)
}

#[test]
fn test_analyze_compare_tabular_arithmetic_7_cmp_10() {
    let base_path = PathBuf::from("examples/analyze/arithmetic");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("policies7.cedar"))
        .arg(base_path.join("policies10.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/compare_7_10.out"), false)
}

#[test]
fn test_analyze_compare_tabular_globs_a_star_cmp_a_star_star() {
    let base_path = PathBuf::from("examples/analyze/globs");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("a_star.cedar"))
        .arg(base_path.join("a_star_star.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/equivalent.out"), false)
}

#[test]
fn test_analyze_compare_tabular_globs_a_star_cmp_a_a_star() {
    let base_path = PathBuf::from("examples/analyze/globs");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("a_star.cedar"))
        .arg(base_path.join("a_a_star.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/more_permissive.out"), false)
}

#[test]
fn test_analyze_compare_tabular_globs_a_star_cmp_a_star_non_a() {
    let base_path = PathBuf::from("examples/analyze/globs");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("a_star.cedar"))
        .arg(base_path.join("a_star_non_a.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/more_permissive.out"), false)
}

#[test]
fn test_analyze_compare_tabular_globs_a_a_star_cmp_a_star_non_a() {
    let base_path = PathBuf::from("examples/analyze/globs");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("a_a_star.cedar"))
        .arg(base_path.join("a_star_non_a.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/less_permissive.out"), false)
}

#[test]
fn test_analyze_compare_tabular_globs_a_star_star_a() {
    let base_path = PathBuf::from("examples/analyze/globs");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("a_star.cedar"))
        .arg(base_path.join("star_a.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/disjoint.out"), false)
}

#[test]
fn test_analyze_compare_tabular_globs_star_a_cmp_star_b() {
    let base_path = PathBuf::from("examples/analyze/globs");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("star_a.cedar"))
        .arg(base_path.join("star_b.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/disjoint.out"), false)
}

#[test]
fn test_analyze_compare_tabular_globs_a_cmp_star_other() {
    let base_path = PathBuf::from("examples/analyze/globs");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("a_star.cedar"))
        .arg(base_path.join("other.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/disjoint.out"), false)
}

#[test]
fn test_analyze_compare_tabular_sets1() {
    let base_path = PathBuf::from("examples/analyze/sets");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("src1.cedar"))
        .arg(base_path.join("tgt1.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/equivalent.out"), false)
}

#[test]
fn test_analyze_compare_tabular_sets2() {
    let base_path = PathBuf::from("examples/analyze/sets");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("src2.cedar"))
        .arg(base_path.join("tgt2.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/equivalent.out"), false)
}

#[test]
fn test_analyze_compare_tabular_sets3() {
    let base_path = PathBuf::from("examples/analyze/sets");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("src3.cedar"))
        .arg(base_path.join("tgt3.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/less_permissive.out"), false)
}

#[test]
fn test_analyze_compare_tabular_sets4() {
    let base_path = PathBuf::from("examples/analyze/sets");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("src4.cedar"))
        .arg(base_path.join("tgt4.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/more_permissive.out"), false)
}

#[test]
fn test_analyze_compare_tabular_sets5a() {
    let base_path = PathBuf::from("examples/analyze/sets");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("src5.cedar"))
        .arg(base_path.join("tgt5a.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/more_permissive.out"), false)
}

#[test]
fn test_analyze_compare_tabular_sets5b() {
    let base_path = PathBuf::from("examples/analyze/sets");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("src5.cedar"))
        .arg(base_path.join("tgt5b.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/more_permissive.out"), false)
}

#[test]
fn test_analyze_compare_tabular_sets5c() {
    let base_path = PathBuf::from("examples/analyze/sets");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("src5.cedar"))
        .arg(base_path.join("tgt5c.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/more_permissive.out"), false)
}

#[test]
fn test_analyze_compare_tabular_sets6() {
    let base_path = PathBuf::from("examples/analyze/sets");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("src6.cedar"))
        .arg(base_path.join("tgt6.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/more_permissive.out"), false)
}

#[test]
fn test_analyze_compare_tabular_sets7a() {
    let base_path = PathBuf::from("examples/analyze/sets");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("src7.cedar"))
        .arg(base_path.join("tgt7a.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/more_permissive.out"), false)
}

#[test]
fn test_analyze_compare_tabular_sets7b() {
    let base_path = PathBuf::from("examples/analyze/sets");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("src7.cedar"))
        .arg(base_path.join("tgt7b.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/disjoint.out"), false)
}

#[test]
fn test_analyze_compare_tabular_misc1() {
    let base_path = PathBuf::from("examples/analyze/misc");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("src1.cedar"))
        .arg(base_path.join("tgt1.cedar"))
        .arg(base_path.join("policies1.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/policies1.out"), false)
}

#[test]
fn test_analyze_policies_tabular_demo1() {
    let base_path = PathBuf::from("examples/analyze/file_share_demo");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("policies")
        .arg(base_path.join("policies1.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/analyze1.out"), false)
}

#[test]
fn test_analyze_policies_tabular_demo2() {
    let base_path = PathBuf::from("examples/analyze/file_share_demo");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("policies")
        .arg(base_path.join("policies2.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/analyze2.out"), false)
}

#[test]
fn test_analyze_policies_tabular_demo3() {
    let base_path = PathBuf::from("examples/analyze/file_share_demo");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("policies")
        .arg(base_path.join("policies3.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/analyze3.out"), false)
}

#[test]
fn test_analyze_policies_tabular_demo4() {
    let base_path = PathBuf::from("examples/analyze/file_share_demo");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("policies")
        .arg(base_path.join("policies4.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/analyze4.out"), false)
}

#[test]
fn test_analyze_compare_tabular_demo_2_1() {
    let base_path = PathBuf::from("examples/analyze/file_share_demo");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("policies2.cedar"))
        .arg(base_path.join("policies1.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/compare_2_1.out"), false)
}

#[test]
fn test_analyze_compare_tabular_demo_3_2() {
    let base_path = PathBuf::from("examples/analyze/file_share_demo");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("policies3.cedar"))
        .arg(base_path.join("policies2.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/compare_3_2.out"), false)
}

#[test]
fn test_analyze_compare_tabular_demo_4_3() {
    let base_path = PathBuf::from("examples/analyze/file_share_demo");

    let output = Command::new("cedar-lean-cli")
        .arg("analyze")
        .arg("compare")
        .arg(base_path.join("policies4.cedar"))
        .arg(base_path.join("policies3.cedar"))
        .arg(base_path.join("policies.cedarschema"))
        .output().expect("Failed to run cedar-lean-cli");

    check_output(output, base_path.join("outputs/tabular/compare_4_3.out"), false)
}