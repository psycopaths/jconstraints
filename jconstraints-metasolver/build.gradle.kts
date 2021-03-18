/*
 * Copyright, TU Dortmund, Malte Mues 2021
 */

group = "tools.aqua"
version = "0.9.6-SNAPSHOT"
description = "jConstraints-metasolver is the solver strategy plug-in for jConstraints"

plugins {
    id("tools.aqua.jconstraints.java-fatjar-convention")
}

dependencies {
    //implementation("com.google.guava:guava:30.1-jre")
    implementation(project(":jconstraints-core"))
    implementation(project(":jconstraints-z3"))
    implementation(project(":jconstraints-cvc4"))
}
