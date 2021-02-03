/*
 * Copyright 2020 TU Dortmund, Malte Mues
 */

import org.gradle.api.tasks.testing.logging.TestLogEvent.*
plugins {
    `java-library`
    `maven-publish`
    id("com.github.hierynomus.license") version "0.15.0"
    id("com.github.johnrengelman.shadow") version "5.2.0"
}

repositories {
    jcenter()
    mavenLocal()
    mavenCentral()
}

group = "tools.aqua"
version = "0.9.6-SNAPSHOT"
description = "jConstraints-z3"

dependencies {
    implementation("io.github.tudo-aqua:z3-turnkey:4.8.7.1")
    implementation("tools.aqua:jconstraints-all:0.9.6-SNAPSHOT")

    testImplementation("org.testng:testng:7.0.0")

}

java {
    toolchain {
        languageVersion.set(JavaLanguageVersion.of(8))
    }
}

val test by tasks.getting(Test::class) {
    useTestNG() {
        useDefaultListeners = true
    }
    testLogging {
        events(FAILED, STANDARD_ERROR, SKIPPED, PASSED)
    }
}


tasks.shadowJar {
    //FIXME: Exclude the other jconstraints-deps
    exclude("tools.aqua:jconstraints-all:.*")
}

license {
    header = rootProject.file("NOTICE")
    strictCheck = true
}
